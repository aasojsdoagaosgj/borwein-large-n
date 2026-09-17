import Borwein.MiddlePhaseDecay
import Borwein.SineCertificate
import Borwein.GaussianNormalization

namespace Borwein.MiddlePhaseCertificate
noncomputable section
open Complex Set MiddlePhaseDecay PhaseIntegral RadialDerivatives SmallBoxPhaseDecay

def lo (k : Fin 16) : ℝ := (8+(k.val:ℝ))/20
def hi (k : Fin 16) : ℝ := (9+(k.val:ℝ))/20
def sineLower (v : ℝ) : ℝ := SineCertificate.polynomial (2*v)-(2:ℝ)*3^23/(23:ℕ).factorial

theorem polynomial_error_three (x : ℝ) (hx : |x| ≤ 3) :
    |Real.sin x-SineCertificate.polynomial x| ≤ (2:ℝ)*3^23/(23:ℕ).factorial := by
  have hb := SineCertificate.sine_error x 23 (by norm_num; linarith)
  rw [SineCertificate.taylor_23] at hb
  apply hb.trans
  unfold SineCertificate.error
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 23
  have hn := div_le_div_of_nonneg_right hp (by positivity : (0:ℝ) ≤ (23:ℕ).factorial)
  nlinarith

theorem sine_lower (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 6/5) : sineLower v ≤ Real.sin (2*v) := by
  have hb := (abs_le.mp (polynomial_error_three (2*v) (by rw [abs_of_nonneg (by positivity)]; linarith))).1
  unfold sineLower
  linarith

set_option maxHeartbeats 3000000 in
theorem cell_numerics (k : Fin 16) :
    0 < sineLower (hi k) ∧
    (13/250:ℝ) < (sineLower (hi k)/(2*hi k))^2/2*(lo k)^2 := by
  fin_cases k <;>
    norm_num [lo,hi,sineLower,SineCertificate.polynomial,Finset.sum_range_succ,Nat.factorial]

theorem cell_curvature (k : Fin 16) : (13/250:ℝ) < curvature (hi k)*(lo k)^2 := by
  have hk : (k.val:ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
  have hk0 : (0:ℝ) ≤ k.val := Nat.cast_nonneg _
  have hv0 : 0 < hi k := by unfold hi; positivity
  have hv1 : hi k ≤ 6/5 := by unfold hi; linarith
  have hb := sine_lower (hi k) hv0.le hv1
  have hc := cell_numerics k
  have hr := div_le_div_of_nonneg_right hb (by positivity : (0:ℝ) ≤ 2*hi k)
  have hs := pow_le_pow_left₀ (div_nonneg hc.1.le (by positivity : (0:ℝ) ≤ 2*hi k)) hr 2
  apply hc.2.trans_le
  unfold curvature
  exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hs (by norm_num)) (sq_nonneg _)

theorem cell_cover (t : ℝ) (ht0 : 2/5 ≤ |t|) (ht1 : |t| ≤ 6/5) :
    ∃ k : Fin 16, lo k ≤ |t| ∧ |t| ≤ hi k := by
  by_cases he : |t| = 6/5
  · refine ⟨15, ?_⟩
    norm_num [lo,hi,he]
  · have hx0 : 0 ≤ 20*|t|-8 := by linarith
    have hx1 : 20*|t|-8 < 16 := by
      rcases ht1.eq_or_lt with heq | hlt
      · exact (he heq).elim
      · linarith
    have hk : ⌊20*|t|-8⌋₊ < 16 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx1)
    refine ⟨⟨⌊20*|t|-8⌋₊,hk⟩,?_⟩
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one (20*|t|-8)
    dsimp [lo,hi]
    constructor <;> linarith

theorem band_real_decay (τ t : ℝ) (hτ : 0 ≤ τ) (ht0 : 2/5 ≤ |t|) (ht1 : |t| ≤ 6/5) :
    (complexR ((τ:ℂ)-(t:ℂ)*I)).re-radialR τ ≤ -(13/250:ℝ)*secondDerivative τ := by
  obtain ⟨k,hk0,hk1⟩ := cell_cover t ht0 ht1
  have hv0 : 0 < hi k := by unfold hi; positivity
  have hkv : (k.val:ℝ) ≤ 15 := by exact_mod_cast (show k.val ≤ 15 by omega)
  have hvp : 2*hi k ≤ Real.pi := by unfold hi; linarith [Real.pi_gt_three]
  have hd := MiddlePhaseDecay.radial_real_decay τ (hi k) t hτ hv0 hvp hk1
  have hlo : 0 ≤ lo k := by unfold lo; positivity
  have hsq := pow_le_pow_left₀ hlo hk0 2
  rw [sq_abs] at hsq
  have hm := mul_le_mul_of_nonneg_left hsq (by unfold curvature; positivity : 0 ≤ curvature (hi k))
  have hc := (cell_curvature k).le.trans hm
  have hV := (secondDerivative_pos τ).le
  have hp := mul_le_mul_of_nonneg_right hc hV
  nlinarith

theorem band_saddle_decay (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ)
    (ht0 : 2/5 ≤ |t|) (ht1 : |t| ≤ 6/5) :
    (saddlePhase n τ t).re ≤ -(13/250:ℝ)*n*secondDerivative τ := by
  have hd := mul_le_mul_of_nonneg_left (band_real_decay τ t hτ ht0 ht1) hn
  unfold saddlePhase
  rw [SmallBoxPhaseDecay.complexR_real]
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.sub_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  nlinarith

theorem band_exponential_bound (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ)
    (ht0 : 2/5 ≤ |t|) (ht1 : |t| ≤ 6/5) :
    ‖Complex.exp (saddlePhase n τ t)‖ ≤ Real.exp (-(13/250:ℝ)*n*secondDerivative τ) := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (band_saddle_decay n τ t hn hτ ht0 ht1)

end
end Borwein.MiddlePhaseCertificate
