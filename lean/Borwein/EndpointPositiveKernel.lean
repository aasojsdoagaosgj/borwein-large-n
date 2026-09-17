import Borwein.EndpointFiniteLocalArc

set_option autoImplicit false

namespace Borwein.EndpointPositiveKernel
noncomputable section
open Complex EndpointPhaseAtoms EndpointActualPhase EndpointEtaBounds

def point (v y : ℝ) : ℂ := exp (-coordinate v y)

theorem point_norm (v y : ℝ) : ‖point v y‖=Real.exp (-v) := by
  rw [point, Complex.norm_exp]
  simp [coordinate]

theorem point_norm_lt_one (v y : ℝ) (hv : 0 < v) : ‖point v y‖ < 1 := by
  rw [point_norm]
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem positive_exponent (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    (-(2*(Real.pi:ℂ)^2/15)/coordinate v y-coordinate v y/6).re ≤ A/v-v/6-1/v := by
  have he : (-(2*(Real.pi:ℂ)^2/15)/coordinate v y-coordinate v y/6).re =
      -5*A*(1/coordinate v y).re-v/6 := by
    simp [A, coordinate, Complex.div_re, Complex.normSq_apply, ← Complex.ofReal_pow]
    ring
  rw [he]
  have hA : 0 ≤ A := by linarith [EndpointDerivativeConstants.A_bounds.1]
  have hr := mul_le_mul_of_nonneg_left (inverse_re_lower v y hv hy) (by positivity : 0 ≤ 5*A)
  have hc : 1-A ≤ 16*A/5 := by linarith [EndpointDerivativeConstants.A_bounds.1]
  have hh := div_le_div_of_nonneg_right hc hv.le
  have hE : 5*A*(16/(25*v))=(16*A/5)/v := by ring
  rw [hE] at hr
  change (16*A/5)/v ≤ 5*A*(1/coordinate v y).re at hr
  have hD : (1-A)/v=1/v-A/v := by ring
  rw [hD] at hh
  linarith

theorem positiveMain_norm (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    ‖positiveMain (coordinate v y)‖ ≤ 3*Real.exp (A/v-v/6)*Real.exp (-1/v) := by
  rw [positiveMain, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Complex.norm_exp]
  have hs : Real.sqrt 5 ≤ (3:ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5), Real.sqrt_nonneg 5]
  have hh := Real.exp_le_exp.mpr (positive_exponent v y hv hy)
  have he : Real.exp (A/v-v/6-1/v)=Real.exp (A/v-v/6)*Real.exp (-1/v) := by rw [← Real.exp_add]; congr 1; ring
  rw [he] at hh
  exact (mul_le_mul hs hh (Real.exp_pos _).le (by norm_num)).trans_eq (by ring)

theorem G_norm (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) :
    ‖EndpointEta.G (point v y)‖ ≤ 6*Real.exp (A/v-v/6)*Real.exp (-1/v) := by
  have hb := normalized_positive_cusp v y hv hV hy
  change ‖EndpointEta.G (point v y)/positiveMain (coordinate v y)-1‖ ≤ 10*Real.exp (-1/v) at hb
  have he := small_exponential v hv hV
  have hp : 0 < ‖positiveMain (coordinate v y)‖ := norm_pos_iff.mpr (positiveMain_ne_zero _)
  have hn : ‖EndpointEta.G (point v y)/positiveMain (coordinate v y)‖ ≤ 2 := by
    have hh := norm_add_le (EndpointEta.G (point v y)/positiveMain (coordinate v y)-1) (1:ℂ)
    simp only [sub_add_cancel, norm_one] at hh
    linarith
  rw [norm_div] at hn
  have hh := (div_le_iff₀ hp).mp hn
  have hm := positiveMain_norm v y hv hy
  nlinarith

end
end Borwein.EndpointPositiveKernel
