import Borwein.RoundedWeightData

namespace Borwein.RoundedWeight
set_option maxRecDepth 16384
noncomputable section
open Borwein.GroupedWeights Borwein.ExpCertificate
open Borwein.RoundedWeightData

theorem D_pos : 0 < (D:ℝ) := by norm_num [D]
theorem W_pos : 0 < (W:ℝ) := by norm_num [W]

theorem denom_homogeneous (n : ℕ) :
    (denom n:ℝ) = (D:ℝ)^4*denominator ((n:ℝ)/D) := by
  unfold denom denominator
  have hp : (D:ℝ) ≠ 0 := ne_of_gt D_pos
  generalize hD : D = K at *
  push_cast
  field_simp [hp]

theorem numer_homogeneous (d : Fin 4) (n : ℕ) :
    (numer d n:ℝ) = (D:ℝ)^7*numerator d ((n:ℝ)/D) := by
  have general (d : Fin 4) (n K : ℕ) (hp : (K:ℝ) ≠ 0) :
      ((![n*K^6+n^3*K^4+n^5*K^2+n^7, n^2*K^5+n^4*K^3+n^6*K,
        n^3*K^4+n^5*K^2, n^4*K^3] d : ℕ):ℝ) =
        (K:ℝ)^7*numerator d ((n:ℝ)/K) := by
    fin_cases d <;> simp only [numerator]
    all_goals push_cast
    all_goals field_simp [hp]
  exact general d n D (ne_of_gt D_pos)

theorem denom_pos (n : ℕ) : 0 < (denom n:ℝ) := by
  rw [denom_homogeneous]
  exact mul_pos (pow_pos D_pos 4) (denominator_pos _ (by positivity))

theorem quotient_homogeneous (d : Fin 4) (l u : ℕ) :
    numerator d ((l:ℝ)/D)/denominator ((u:ℝ)/D)^2 =
      (D:ℝ)*(numer d l:ℝ)/(denom u:ℝ)^2 := by
  rw [numer_homogeneous, denom_homogeneous]
  have h : denominator ((u:ℝ)/D) ≠ 0 := ne_of_gt (denominator_pos _ (by positivity))
  have hp : (D:ℝ) ≠ 0 := ne_of_gt D_pos
  generalize hD : D = K at *
  field_simp [h, hp]

theorem origin_lower (d : Fin 4) (a : ℕ) (h : a*25 ≤ (4-d.val)*W) :
    (a:ℝ)/W ≤ (4-(d:ℝ))/25 := by
  have hd : d.val ≤ 4 := by omega
  have hh : (a:ℝ)*25 ≤ (4-(d:ℝ))*(W:ℝ) := by
    exact_mod_cast h
  rw [div_le_div_iff₀ W_pos (by norm_num)]
  exact hh

theorem origin_upper (d : Fin 4) (a : ℕ) (h : (4-d.val)*W ≤ a*25) :
    (4-(d:ℝ))/25 ≤ (a:ℝ)/W := by
  have hd : d.val ≤ 4 := by omega
  have hh : (4-(d:ℝ))*(W:ℝ) ≤ (a:ℝ)*25 := by
    exact_mod_cast h
  rw [div_le_div_iff₀ (by norm_num) W_pos]
  exact hh

theorem ratio_lower (d : Fin 4) (a l u : ℕ)
    (h : a*(denom u)^2 ≤ W*D*numer d l) :
    (a:ℝ)/W ≤ numerator d ((l:ℝ)/D)/denominator ((u:ℝ)/D)^2 := by
  rw [quotient_homogeneous, div_le_div_iff₀ W_pos (pow_pos (denom_pos u) 2)]
  have hh : (a:ℝ)*(denom u:ℝ)^2 ≤ (W:ℝ)*D*(numer d l:ℝ) := by exact_mod_cast h
  nlinarith

theorem ratio_upper (d : Fin 4) (a l u : ℕ)
    (h : W*D*numer d u ≤ a*(denom l)^2) :
    numerator d ((u:ℝ)/D)/denominator ((l:ℝ)/D)^2 ≤ (a:ℝ)/W := by
  rw [quotient_homogeneous, div_le_div_iff₀ (pow_pos (denom_pos l) 2) W_pos]
  have hh : (W:ℝ)*D*(numer d u:ℝ) ≤ (a:ℝ)*(denom l:ℝ)^2 := by exact_mod_cast h
  nlinarith

theorem checker_sound (d : Fin 4) (i : ℕ) (hi : i < 400) (hc : Checks d i) :
    (lo d i:ℝ)/W ≤ envelope d ((113/40000:ℝ)+(11/2:ℝ)*((i+1:ℕ):ℝ)/400) ∧
    envelope d ((113/40000:ℝ)+(11/2:ℝ)*((i+1:ℕ):ℝ)/400) ≤ (RoundedWeightData.hi d i:ℝ)/W := by
  have he := Borwein.RoundedExponent.all_401_bounds (i+1) hi
  have hw := weight_enclosure d _ _ _ (show 0 ≤ Borwein.RoundedExponent.lower (i+1) by
    unfold Borwein.RoundedExponent.lower
    exact div_nonneg (Nat.cast_nonneg _) (by norm_num [scale])) he.1 he.2
  have hr := Borwein.SmoothedCertificate.radial_at_zero d
  unfold Checks at hc
  unfold envelope
  rw [hr]
  constructor
  · apply le_min (origin_lower d _ hc.1)
    exact le_trans (ratio_lower d _ _ _ hc.2.1) hw.1
  · rcases hc.2.2 with h | h
    · exact le_trans (min_le_left _ _) (origin_upper d _ h)
    · exact le_trans (min_le_right _ _) (le_trans hw.2 (ratio_upper d _ _ _ h))

end
end Borwein.RoundedWeight
