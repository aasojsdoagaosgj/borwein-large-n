import Borwein.PhaseGap
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Connect normalized phase gaps to logarithmic integrals of the five-term sum. -/

namespace Borwein.PhaseIntegral

noncomputable section
open scoped BigOperators
open Borwein.PhaseGap MeasureTheory

def radialSum (y : ℝ) : ℝ := ∑ j : Fin 5, Real.exp (-(j : ℝ) * y)

def fiveSum (z : ℂ) : ℂ := ∑ j : Fin 5, Complex.exp (-z) ^ (j : ℕ)

theorem fiveSum_eq_exp_sum (z : ℂ) :
    fiveSum z = ∑ j : Fin 5, Complex.exp (-(j : ℂ) * z) := by
  unfold fiveSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem fiveSum_real (y : ℝ) : fiveSum (y : ℂ) = (radialSum y : ℂ) := by
  simp [fiveSum_eq_exp_sum, radialSum, Fin.sum_univ_five, Complex.ofReal_exp]

theorem phase_eq_fiveSum_div (τ t x : ℝ) :
    phase τ t x = fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I) * (x : ℂ)) /
      (radialSum (τ*x) : ℂ) := by
  rw [phase, radial_amplitude_eq_geometric]
  unfold fiveSum radialSum
  congr 2
  funext j
  congr 2
  push_cast
  ring

theorem fiveSum_ne_zero (τ t x : ℝ) (hτ : 0 < τ) (hx : 0 ≤ x) :
    fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I) * (x : ℂ)) ≠ 0 := by
  have hz := phase_ne_zero τ t x hτ hx
  rw [phase_eq_fiveSum_div] at hz
  intro hzero
  exact hz (by rw [hzero, zero_div])

theorem neg_log_phase (τ t x : ℝ) (hτ : 0 < τ) (hx : 0 ≤ x) :
    -Real.log ‖phase τ t x‖ = Real.log (radialSum (τ*x)) -
      Real.log ‖fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I) * (x : ℂ))‖ := by
  have hd : 0 < radialSum (τ*x) := radialDenominator_pos (τ*x)
  rw [phase_eq_fiveSum_div, norm_div,
    Complex.norm_real, Real.norm_of_nonneg hd.le,
    Real.log_div (norm_ne_zero_iff.mpr (fiveSum_ne_zero τ t x hτ hx))
      (ne_of_gt hd)]
  ring

theorem continuous_radialSum : Continuous radialSum := by
  unfold radialSum
  fun_prop

theorem continuous_fiveSum : Continuous fiveSum := by
  unfold fiveSum
  fun_prop

theorem continuous_log_radialSum (τ : ℝ) :
    Continuous (fun x : ℝ => Real.log (radialSum (τ*x))) := by
  apply Continuous.log
  · exact continuous_radialSum.comp (continuous_const.mul continuous_id)
  · intro x; exact ne_of_gt (radialDenominator_pos (τ*x))

theorem continuousOn_log_norm_fiveSum (τ t : ℝ) (hτ : 0 < τ) :
    ContinuousOn (fun x : ℝ => Real.log
      ‖fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I) * (x : ℂ))‖) (Set.Icc 0 1) := by
  apply ContinuousOn.log
  · apply Continuous.continuousOn
    have : Continuous (fun x : ℝ => fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I) * (x : ℂ))) := by
      exact continuous_fiveSum.comp (by fun_prop)
    exact this.norm
  · intro x hx
    exact norm_ne_zero_iff.mpr (fiveSum_ne_zero τ t x hτ hx.1)

def radialR (τ : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, Real.log (radialSum (τ*x))

def modulusR (z : ℂ) : ℝ := ∫ x in (0 : ℝ)..1, Real.log ‖fiveSum (z*(x : ℂ))‖

theorem integral_phase_eq_R_difference (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖) =
      radialR τ - modulusR ((τ : ℂ) - (t : ℂ)*Complex.I) := by
  rw [radialR, modulusR, ← intervalIntegral.integral_sub
    ((continuous_log_radialSum τ).intervalIntegrable 0 1)
    ((continuousOn_log_norm_fiveSum τ t hτ).intervalIntegrable_of_Icc (by norm_num))]
  apply intervalIntegral.integral_congr
  intro x hx
  exact neg_log_phase τ t x hτ (by simpa using hx.1)

theorem R_difference_ge_quadratic (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      radialR τ - modulusR ((τ : ℂ) - (t : ℂ)*Complex.I) := by
  rw [← integral_phase_eq_R_difference τ t hτ]
  exact integral_phase_gap τ t hτ

/-- The principal logarithm is measurable and bounded by the continuous logarithmic norm
plus π. No unproved continuity across its branch cut is used. -/
theorem intervalIntegrable_clog (f : ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (hf : Continuous f) (hlog : ContinuousOn (fun x => Real.log ‖f x‖) (Set.Icc a b)) :
    IntervalIntegrable (fun x => Complex.log (f x)) volume a b := by
  have hbound : IntervalIntegrable (fun x => |Real.log ‖f x‖| + Real.pi) volume a b :=
    (hlog.abs.add continuousOn_const).intervalIntegrable_of_Icc hab
  apply hbound.mono_fun' (Complex.measurable_log.comp hf.measurable).aestronglyMeasurable
  apply ae_of_all
  intro x
  calc
    ‖Complex.log (f x)‖ ≤ |(Complex.log (f x)).re| + |(Complex.log (f x)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ |Real.log ‖f x‖| + Real.pi := by
      rw [Complex.log_re, Complex.log_im]
      exact add_le_add le_rfl (Complex.abs_arg_le_pi _)

def complexR (z : ℂ) : ℂ := ∫ x in (0 : ℝ)..1, Complex.log (fiveSum (z*(x : ℂ)))

theorem intervalIntegrable_complexR_density (τ t : ℝ) (hτ : 0 < τ) :
    IntervalIntegrable (fun x : ℝ => Complex.log
      (fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I)*(x : ℂ)))) volume 0 1 := by
  apply intervalIntegrable_clog _ 0 1 (by norm_num)
  · exact continuous_fiveSum.comp (by fun_prop)
  · exact continuousOn_log_norm_fiveSum τ t hτ

theorem modulusR_eq_re_complexR (τ t : ℝ) (hτ : 0 < τ) :
    modulusR ((τ : ℂ) - (t : ℂ)*Complex.I) =
      (complexR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  have h := intervalIntegral.intervalIntegral_re (intervalIntegrable_complexR_density τ t hτ)
  simpa [modulusR, complexR, Complex.log_re] using h

/-- Exact normalization identity with the explicitly defined complex logarithmic integral. -/
theorem integral_phase_eq_R_re_difference (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖) =
      radialR τ - (complexR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  rw [integral_phase_eq_R_difference τ t hτ, modulusR_eq_re_complexR τ t hτ]

theorem R_re_difference_ge_quadratic (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      radialR τ - (complexR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  rw [← integral_phase_eq_R_re_difference τ t hτ]
  exact integral_phase_gap τ t hτ

theorem radialR_zero : radialR 0 = Real.log 5 := by
  simp [radialR, radialSum]

/-- A branch-independent real-part bridge, also usable at τ=0 whenever the phase is nonzero. -/
theorem integral_phase_eq_R_re_difference_of_ne_zero (τ t : ℝ)
    (hz : ∀ x ∈ Set.Icc (0 : ℝ) 1, phase τ t x ≠ 0) :
    (∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖) =
      radialR τ - (complexR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  let f : ℝ → ℂ := fun x => fiveSum (((τ : ℂ) - (t : ℂ)*Complex.I)*(x : ℂ))
  have hfn : ∀ x ∈ Set.Icc (0 : ℝ) 1, f x ≠ 0 := by
    intro x hx hzero
    apply hz x hx
    rw [phase_eq_fiveSum_div, show fiveSum
      (((τ : ℂ) - (t : ℂ)*Complex.I)*(x : ℂ)) = 0 from hzero, zero_div]
  have hfc : Continuous f := continuous_fiveSum.comp (by fun_prop)
  have hlog : ContinuousOn (fun x => Real.log ‖f x‖) (Set.Icc (0 : ℝ) 1) :=
    hfc.norm.continuousOn.log (fun x hx => norm_ne_zero_iff.mpr (hfn x hx))
  have hint := intervalIntegrable_clog f 0 1 (by norm_num) hfc hlog
  have hre : (∫ x in (0 : ℝ)..1, Real.log ‖f x‖) =
      (∫ x in (0 : ℝ)..1, Complex.log (f x)).re := by
    simpa [Complex.log_re] using intervalIntegral.intervalIntegral_re hint
  calc
    (∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖) =
        ∫ x in (0 : ℝ)..1, Real.log (radialSum (τ*x)) - Real.log ‖f x‖ := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hxi : x ∈ Set.Icc (0 : ℝ) 1 := by simpa using hx
      have hd : 0 < radialSum (τ*x) := radialDenominator_pos (τ*x)
      change -Real.log ‖phase τ t x‖ = Real.log (radialSum (τ*x)) - Real.log ‖f x‖
      rw [phase_eq_fiveSum_div]
      change -Real.log ‖f x / (radialSum (τ*x) : ℂ)‖ = _
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le,
        Real.log_div (norm_ne_zero_iff.mpr (hfn x hxi)) (ne_of_gt hd)]
      ring
    _ = radialR τ - (complexR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
      rw [intervalIntegral.integral_sub
        ((continuous_log_radialSum τ).intervalIntegrable 0 1)
        (hlog.intervalIntegrable_of_Icc (by norm_num)), hre]
      rfl

end
end Borwein.PhaseIntegral
