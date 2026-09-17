import Borwein.LogKernel
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues

/-! The dilogarithm representation of the logarithmic kernel, with dominated convergence at x=0. -/

namespace Borwein.Dilogarithm
noncomputable section
open scoped BigOperators
open Borwein.LogKernel MeasureTheory

def term (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-(n : ℂ)*z*(x : ℂ)) / (n : ℂ)

def bound (τ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-(n : ℝ)*τ*x) / (n : ℝ)

theorem term_real (τ : ℝ) (n : ℕ) (x : ℝ) : term (τ : ℂ) n x = (bound τ n x : ℂ) := by
  simp [term, bound, Complex.ofReal_div, Complex.ofReal_exp]

theorem norm_term (z : ℂ) (n : ℕ) (x : ℝ) : ‖term z n x‖ = bound z.re n x := by
  simp [term, bound, Complex.norm_exp, Complex.mul_re, Complex.neg_re]

theorem continuous_term (z : ℂ) (n : ℕ) : Continuous (term z n) := by
  unfold term
  fun_prop

theorem hasSum_term (z : ℂ) (x : ℝ) (hz : 0 < z.re) (hx : 0 < x) :
    HasSum (fun n => term z n x) (-Complex.log (kernel z x)) := by
  have hnorm : ‖Complex.exp (-z*(x : ℂ))‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff]
    simpa using mul_neg_of_neg_of_pos (neg_neg_of_pos hz) hx
  unfold kernel
  convert Complex.hasSum_taylorSeries_neg_log hnorm using 1
  ext n
  unfold term
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem hasSum_bound (τ x : ℝ) (hτ : 0 < τ) (hx : 0 < x) :
    HasSum (fun n => bound τ n x) (-Real.log ‖kernel (τ : ℂ) x‖) := by
  have h := Complex.hasSum_re (hasSum_term (τ : ℂ) x (by simpa using hτ) hx)
  simpa only [term_real, Complex.ofReal_re, Complex.neg_re, Complex.log_re] using h

theorem intervalIntegrable_tsum_bound (τ : ℝ) (hτ : 0 < τ) :
    IntervalIntegrable (fun x => ∑' n, bound τ n x) volume 0 1 := by
  have heq : Set.EqOn (fun x => ∑' n, bound τ n x)
      (fun x => -Real.log ‖kernel (τ : ℂ) x‖) (Set.uIoo (0 : ℝ) 1) := by
    intro x hx
    have hxi : x ∈ Set.Ioo (0 : ℝ) 1 := by simpa using hx
    exact (hasSum_bound τ x hτ hxi.1).tsum_eq
  apply (intervalIntegrable_congr_uIoo heq).mpr
  exact (intervalIntegrable_log_norm_kernel (τ : ℂ) 0 1).neg

/-- The integrated logarithmic series is justified despite its singularity at the left endpoint. -/
theorem hasSum_integral_term (z : ℂ) (hz : 0 < z.re) :
    HasSum (fun n => ∫ x in (0 : ℝ)..1, term z n x) (-hIntegral z) := by
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume)
    (F := term z) (f := fun x => -Complex.log (kernel z x)) (bound z.re)
    (fun n => (continuous_term z n).aestronglyMeasurable) (by
      intro n
      exact ae_of_all _ (fun x _ => (norm_term z n x).le)) (by
      apply ae_of_all
      intro x hx
      have hxi : x ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hx
      exact (hasSum_bound z.re x hz hxi.1).summable)
    (intervalIntegrable_tsum_bound z.re hz) (by
      apply ae_of_all
      intro x hx
      have hxi : x ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hx
      exact hasSum_term z x hz hxi.1)
  simpa [hIntegral, intervalIntegral.integral_neg] using h

theorem integral_term (z : ℂ) (n : ℕ) (hz : 0 < z.re) :
    (∫ x in (0 : ℝ)..1, term z n x) =
      (1 - Complex.exp (-(n : ℂ)*z)) / ((n : ℂ)^2*z) := by
  by_cases hn : n = 0
  · subst n; simp [term]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hzC : z ≠ 0 := by
    intro he
    simp [he] at hz
  simp only [term, intervalIntegral.integral_div]
  rw [integral_exp_mul_complex (mul_ne_zero (neg_ne_zero.mpr hnC) hzC)]
  simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
  field_simp
  ring

def dilog (q : ℂ) : ℂ := ∑' n : ℕ, q^n / (n : ℂ)^2

theorem summable_dilog (q : ℂ) (hq : ‖q‖ ≤ 1) :
    Summable (fun n : ℕ => q^n / (n : ℂ)^2) := by
  apply hasSum_zeta_two.summable.of_norm_bounded
  intro n
  simp only [norm_div, norm_pow, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
  exact pow_le_one₀ (norm_nonneg q) hq

theorem hasSum_dilog (q : ℂ) (hq : ‖q‖ ≤ 1) :
    HasSum (fun n : ℕ => q^n / (n : ℂ)^2) (dilog q) :=
  (summable_dilog q hq).hasSum

theorem hasSum_basel_complex :
    HasSum (fun n : ℕ => (1 : ℂ)/(n : ℂ)^2) ((Real.pi : ℂ)^2/6) := by
  have h := Complex.hasSum_ofReal.mpr hasSum_zeta_two
  simpa using h

theorem dilog_one : dilog 1 = (Real.pi : ℂ)^2/6 := by
  simpa [dilog] using hasSum_basel_complex.tsum_eq

/-- The exact dilogarithm identity on the right half-plane, without external numerical premises. -/
theorem hIntegral_eq_dilog (z : ℂ) (hz : 0 < z.re) :
    hIntegral z = (dilog (Complex.exp (-z)) - (Real.pi : ℂ)^2/6) / z := by
  have hq : ‖Complex.exp (-z)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    simpa using le_of_lt (neg_neg_of_pos hz)
  have hs := (hasSum_basel_complex.sub (hasSum_dilog (Complex.exp (-z)) hq)).div_const z
  have hclosed : HasSum
      (fun n : ℕ => (1 - Complex.exp (-(n : ℂ)*z)) / ((n : ℂ)^2*z))
      (((Real.pi : ℂ)^2/6 - dilog (Complex.exp (-z))) / z) := by
    apply hs.congr_fun
    intro n
    rw [← Complex.exp_nat_mul]
    have he : -(n : ℂ)*z = (n : ℂ)*(-z) := by ring
    rw [he]
    ring
  have hi : HasSum
      (fun n : ℕ => (1 - Complex.exp (-(n : ℂ)*z)) / ((n : ℂ)^2*z)) (-hIntegral z) := by
    simpa only [integral_term z _ hz] using hasSum_integral_term z hz
  have he := hi.unique hclosed
  calc
    hIntegral z = -(-hIntegral z) := by ring
    _ = -(((Real.pi : ℂ)^2/6 - dilog (Complex.exp (-z))) / z) := congrArg Neg.neg he
    _ = (dilog (Complex.exp (-z)) - (Real.pi : ℂ)^2/6) / z := by ring

theorem kernelR_eq_dilog (z : ℂ) (hz : 0 < z.re) :
    kernelR z =
      (dilog (Complex.exp (-(5*z))) - (Real.pi : ℂ)^2/6) / (5*z) -
      (dilog (Complex.exp (-z)) - (Real.pi : ℂ)^2/6) / z := by
  unfold kernelR
  rw [hIntegral_eq_dilog _ (by simpa using mul_pos (by norm_num : (0 : ℝ)<5) hz),
    hIntegral_eq_dilog z hz]

end
end Borwein.Dilogarithm
