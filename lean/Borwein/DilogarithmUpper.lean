import Borwein.Dilogarithm

set_option autoImplicit false

namespace Borwein.DilogarithmUpper
noncomputable section
open Complex MeasureTheory Dilogarithm LogKernel

def radial (τ : ℝ) : ℝ := ∑' k : ℕ, (Real.exp (-τ))^k/(k:ℝ)^2

theorem radial_summable (τ : ℝ) (hτ : 0 ≤ τ) :
    Summable (fun k : ℕ => (Real.exp (-τ))^k/(k:ℝ)^2) := by
  apply hasSum_zeta_two.summable.of_norm_bounded
  intro k
  rw [Real.norm_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (k:ℝ))
  exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))

theorem radial_nonneg (τ : ℝ) : 0 ≤ radial τ := by unfold radial; exact tsum_nonneg (fun k => by positivity)

theorem radial_mono {τ σ : ℝ} (hτ : 0 ≤ τ) (hτσ : τ ≤ σ) : radial σ ≤ radial τ := by
  apply (radial_summable σ (hτ.trans hτσ)).tsum_le_tsum _ (radial_summable τ hτ)
  intro k
  apply div_le_div_of_nonneg_right _ (sq_nonneg (k:ℝ))
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  exact Real.exp_le_exp.mpr (by linarith)

theorem dilog_radial (τ : ℝ) (hτ : 0 ≤ τ) :
    dilog (Complex.exp (-(τ:ℂ))) = (radial τ:ℂ) := by
  have hs := Complex.hasSum_ofReal.mpr (radial_summable τ hτ).hasSum
  have hc : HasSum (fun k : ℕ => (Complex.exp (-(τ:ℂ)))^k/(k:ℂ)^2) (radial τ:ℂ) := by
    simpa [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_exp,radial] using hs
  exact hc.tsum_eq

theorem norm_dilog_le (z : ℂ) (hz : 0 ≤ z.re) :
    ‖dilog (Complex.exp (-z))‖ ≤ radial z.re := by
  have hq : ‖Complex.exp (-z)‖ ≤ 1 := by
    rw [Complex.norm_exp,Real.exp_le_one_iff]
    simpa using neg_nonpos.mpr hz
  have h := norm_tsum_le_tsum_norm (summable_dilog (Complex.exp (-z)) hq).norm
  simpa [dilog,radial,norm_div,norm_pow,Complex.norm_exp,Complex.norm_natCast] using h

theorem quadratic_bound (A τ r B : ℝ) (hA : 0 < A) (hτ : 0 < τ) (hr : 0 < r) :
    B/r-A*τ/r^2 ≤ B^2/(4*A*τ) := by
  have he : B^2/(4*A*τ)-(B/r-A*τ/r^2) = (B*r-2*A*τ)^2/(4*A*τ*r^2) := by
    field_simp
    ring
  have hp : 0 ≤ (B*r-2*A*τ)^2/(4*A*τ*r^2) := by positivity
  rw [← he] at hp
  linarith

theorem quotient_bound (W z : ℂ) (A B : ℝ) (hA : 0 < A) (hz : 0 < z.re) (hW : ‖W‖ ≤ B) :
    ((W-(A:ℂ))/z).re ≤ B^2/(4*A*z.re) := by
  have hzn : z ≠ 0 := by intro h; simp [h] at hz
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hzn
  have hw : (W/z).re ≤ B/‖z‖ := (Complex.re_le_norm (W/z)).trans (by
    rw [norm_div]
    exact div_le_div_of_nonneg_right hW hr.le)
  have ha : ((A:ℂ)/z).re = A*z.re/‖z‖^2 := by
    simp [Complex.div_re,Complex.sq_norm]
  rw [sub_div,Complex.sub_re,ha]
  exact (sub_le_sub_right hw _).trans (quadratic_bound A z.re ‖z‖ B hA hz hr)

theorem hIntegral_upper (z : ℂ) (hz : 0 < z.re) :
    (hIntegral z).re ≤ (radial z.re)^2/(4*(Real.pi^2/6)*z.re) := by
  rw [hIntegral_eq_dilog z hz]
  have h := quotient_bound (dilog (Complex.exp (-z))) z (Real.pi^2/6) (radial z.re)
    (by positivity) hz (norm_dilog_le z hz.le)
  simpa using h

end
end Borwein.DilogarithmUpper
