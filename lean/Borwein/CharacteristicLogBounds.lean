import Borwein.CharacteristicLogDerivatives

namespace Borwein.CharacteristicLogBounds
noncomputable section
open Complex CenteredCharacteristic CharacteristicLogDerivatives RadialMoments CentralMoments

theorem quotient_bound (z w : ℂ) (a b : ℝ) (hz : ‖z‖ ≤ a) (hw : b ≤ ‖w‖)
    (hb : 0 < b) : ‖z/w‖ ≤ a/b := by
  rw [norm_div]
  exact div_le_div₀ ((norm_nonneg z).trans hz) hz hb hw

theorem jet_bounds (y t : ℝ) (ht : |t| ≤ 2/5) :
    (69/100:ℝ) ≤ ‖jet 0 y t‖ ∧
    ‖jet 1 y t‖ ≤ (2/5:ℝ)*variance y ∧
    ‖jet 2 y t‖ ≤ variance y ∧
    ‖jet 3 y t‖ ≤ 4*variance y ∧
    ‖jet 4 y t‖ ≤ 16*variance y := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [jet_zero]; exact characteristic_norm_lower y t ht
  · rw [jet_norm]
    exact (first_moment_bound y t).trans (mul_le_mul_of_nonneg_right ht (variance_pos y).le)
  · simpa only [jet_norm,pow_zero,one_mul] using higher_moment_bound 0 y t
  · simpa only [jet_norm,pow_one] using higher_moment_bound 1 y t
  · simpa only [jet_norm,show (4:ℝ)^2=16 by norm_num] using higher_moment_bound 2 y t

theorem variance_power_bounds (y : ℝ) : variance y^2 ≤ 4*variance y ∧
    variance y^3 ≤ 16*variance y ∧ variance y^4 ≤ 64*variance y := by
  have hv := variance_le_four y
  have hv0 := (variance_pos y).le
  have h2 : variance y^2 ≤ 4*variance y := by nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hv0
  have h4 := mul_le_mul_of_nonneg_left h3 hv0
  constructor
  · exact h2
  constructor <;> nlinarith

theorem log_third_bound (y t : ℝ) (ht : |t| ≤ 2/5) :
    ‖logThird y t‖ ≤ 23*variance y := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := jet_bounds y t ht
  have hv0 := (variance_pos y).le
  have hp := variance_power_bounds y
  have h02 : (69/100:ℝ)^2 ≤ ‖(jet 0 y t)^2‖ := by
    rw [norm_pow]; exact pow_le_pow_left₀ (by norm_num) h0 2
  have h03 : (69/100:ℝ)^3 ≤ ‖(jet 0 y t)^3‖ := by
    rw [norm_pow]; exact pow_le_pow_left₀ (by norm_num) h0 3
  have ha := quotient_bound (jet 3 y t) (jet 0 y t) (4*variance y) (69/100) h3 h0 (by norm_num)
  have hb := quotient_bound (3*jet 2 y t*jet 1 y t) ((jet 0 y t)^2)
    (3*variance y*((2/5)*variance y)) ((69/100)^2) (by
      simp only [norm_mul]; norm_num; gcongr) h02 (by norm_num)
  have hc := quotient_bound (2*(jet 1 y t)^3) ((jet 0 y t)^3)
    (2*((2/5)*variance y)^3) ((69/100)^3) (by
      simp only [norm_mul,norm_pow]; norm_num; gcongr) h03 (by norm_num)
  have hs := (norm_add_le
    (jet 3 y t/jet 0 y t-3*jet 2 y t*jet 1 y t/(jet 0 y t)^2)
    (2*(jet 1 y t)^3/(jet 0 y t)^3)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  change ‖logThird y t‖ ≤ _ at hs
  have hf := hs.trans (add_le_add (add_le_add ha hb) hc)
  norm_num at hf
  ring_nf at hf
  nlinarith only [hf,hp.1,hp.2.1,hv0]

theorem log_fourth_bound (y t : ℝ) (ht : |t| ≤ 2/5) :
    ‖logFourth y t‖ ≤ 240*variance y := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := jet_bounds y t ht
  have hv0 := (variance_pos y).le
  have hp := variance_power_bounds y
  have hd (k : ℕ) : (69/100:ℝ)^k ≤ ‖(jet 0 y t)^k‖ := by
    rw [norm_pow]; exact pow_le_pow_left₀ (by norm_num) h0 k
  have ha := quotient_bound (jet 4 y t) (jet 0 y t) (16*variance y) (69/100) h4 h0 (by norm_num)
  have hb := quotient_bound (4*jet 3 y t*jet 1 y t) ((jet 0 y t)^2)
    (4*(4*variance y)*((2/5)*variance y)) ((69/100)^2) (by
      simp only [norm_mul]; norm_num; gcongr) (hd 2) (by norm_num)
  have hc := quotient_bound (3*(jet 2 y t)^2) ((jet 0 y t)^2)
    (3*(variance y)^2) ((69/100)^2) (by
      simp only [norm_mul,norm_pow]; norm_num; gcongr) (hd 2) (by norm_num)
  have he := quotient_bound (12*jet 2 y t*(jet 1 y t)^2) ((jet 0 y t)^3)
    (12*variance y*((2/5)*variance y)^2) ((69/100)^3) (by
      simp only [norm_mul,norm_pow]; norm_num; gcongr) (hd 3) (by norm_num)
  have hf := quotient_bound (6*(jet 1 y t)^4) ((jet 0 y t)^4)
    (6*((2/5)*variance y)^4) ((69/100)^4) (by
      simp only [norm_mul,norm_pow]; norm_num; gcongr) (hd 4) (by norm_num)
  have hs : ‖logFourth y t‖ ≤
      ‖jet 4 y t/jet 0 y t‖+‖4*jet 3 y t*jet 1 y t/(jet 0 y t)^2‖+
      ‖3*(jet 2 y t)^2/(jet 0 y t)^2‖+‖12*jet 2 y t*(jet 1 y t)^2/(jet 0 y t)^3‖+
      ‖6*(jet 1 y t)^4/(jet 0 y t)^4‖ := by
    unfold logFourth
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)) le_rfl)
  have ht := hs.trans (add_le_add (add_le_add (add_le_add (add_le_add ha hb) hc) he) hf)
  norm_num at ht
  ring_nf at ht
  nlinarith only [ht,hp.1,hp.2.1,hp.2.2,hv0]

end
end Borwein.CharacteristicLogBounds
