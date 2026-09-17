import Borwein.RadialMoments
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! First and second derivatives of R, justified by dominated differentiation on the full real line. -/

namespace Borwein.RadialDerivatives
noncomputable section
open Borwein.RadialMoments Borwein.PhaseIntegral MeasureTheory

def firstDensity (τ x : ℝ) : ℝ := -x * mean (τ*x)
def secondDensity (τ x : ℝ) : ℝ := x^2 * variance (τ*x)
def firstDerivative (τ : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, firstDensity τ x
def secondDerivative (τ : ℝ) : ℝ := ∫ x in (0 : ℝ)..1, secondDensity τ x

theorem hasDerivAt_log_density (τ x : ℝ) :
    HasDerivAt (fun u => Real.log (radialSum (u*x))) (firstDensity τ x) τ := by
  have h := (hasDerivAt_log_radialSum (τ*x)).comp τ ((hasDerivAt_id τ).mul_const x)
  apply h.congr_deriv
  simp only [firstDensity]
  ring

theorem hasDerivAt_firstDensity (τ x : ℝ) :
    HasDerivAt (fun u => firstDensity u x) (secondDensity τ x) τ := by
  have h := ((hasDerivAt_mean (τ*x)).comp τ ((hasDerivAt_id τ).mul_const x)).const_mul (-x)
  apply h.congr_deriv
  simp only [secondDensity]
  ring

theorem continuous_firstDensity (τ : ℝ) : Continuous (firstDensity τ) := by
  unfold firstDensity
  fun_prop

theorem continuous_secondDensity (τ : ℝ) : Continuous (secondDensity τ) := by
  unfold secondDensity
  fun_prop

theorem norm_firstDensity_le (τ x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖firstDensity τ x‖ ≤ 4 := by
  unfold firstDensity
  rw [neg_mul, norm_neg, Real.norm_of_nonneg (mul_nonneg hx.1 (mean_nonneg _))]
  calc
    x * mean (τ*x) ≤ 1*4 := mul_le_mul hx.2 (mean_le_four _) (mean_nonneg _) (by norm_num)
    _ = 4 := by ring

theorem norm_secondDensity_le (τ x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ‖secondDensity τ x‖ ≤ 16 := by
  unfold secondDensity
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (variance_pos _).le)]
  have hxs : x^2 ≤ 1 := by nlinarith [hx.1, hx.2]
  calc
    x^2 * variance (τ*x) ≤ 1*16 :=
      mul_le_mul hxs (variance_le_sixteen _) (variance_pos _).le (by norm_num)
    _ = 16 := by ring

theorem hasDerivAt_radialR (τ : ℝ) : HasDerivAt radialR (firstDerivative τ) τ := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume) (x₀ := τ) (s := Set.univ)
    (F := fun u x => Real.log (radialSum (u*x))) (F' := firstDensity) (bound := fun _ => (4 : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall (fun u => (continuous_log_radialSum u).aestronglyMeasurable))
    ((continuous_log_radialSum τ).intervalIntegrable 0 1) (continuous_firstDensity τ).aestronglyMeasurable
    (by
      apply ae_of_all
      intro x hx u _
      have hxi : x ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hx
      exact norm_firstDensity_le u x ⟨hxi.1.le, hxi.2⟩)
    intervalIntegrable_const (by
      apply ae_of_all
      intro x _ u _
      exact hasDerivAt_log_density u x)
  exact h.2

theorem hasDerivAt_firstDerivative (τ : ℝ) :
    HasDerivAt firstDerivative (secondDerivative τ) τ := by
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (a := (0 : ℝ)) (b := (1 : ℝ)) (μ := volume) (x₀ := τ) (s := Set.univ)
    (F := firstDensity) (F' := secondDensity) (bound := fun _ => (16 : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall (fun u => (continuous_firstDensity u).aestronglyMeasurable))
    ((continuous_firstDensity τ).intervalIntegrable 0 1) (continuous_secondDensity τ).aestronglyMeasurable
    (by
      apply ae_of_all
      intro x hx u _
      have hxi : x ∈ Set.Ioc (0 : ℝ) 1 := by simpa using hx
      exact norm_secondDensity_le u x ⟨hxi.1.le, hxi.2⟩)
    intervalIntegrable_const (by
      apply ae_of_all
      intro x _ u _
      exact hasDerivAt_firstDensity u x)
  exact h.2

theorem secondDerivative_pos (τ : ℝ) : 0 < secondDerivative τ := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_secondDensity τ).intervalIntegrable 0 1) _ (by norm_num)
  intro x hx
  exact mul_pos (sq_pos_of_pos hx.1) (variance_pos (τ*x))

theorem deriv_radialR (τ : ℝ) : deriv radialR τ = firstDerivative τ :=
  (hasDerivAt_radialR τ).deriv

theorem deriv_two_radialR (τ : ℝ) : deriv (deriv radialR) τ = secondDerivative τ := by
  rw [show deriv radialR = firstDerivative from funext deriv_radialR]
  exact (hasDerivAt_firstDerivative τ).deriv

theorem deriv_two_radialR_pos (τ : ℝ) : 0 < deriv (deriv radialR) τ := by
  rw [deriv_two_radialR]
  exact secondDerivative_pos τ

theorem strictMono_firstDerivative : StrictMono firstDerivative :=
  strictMono_of_hasDerivAt_pos hasDerivAt_firstDerivative secondDerivative_pos

theorem firstDerivative_zero : firstDerivative 0 = -1 := by
  norm_num [firstDerivative, firstDensity, mean_zero, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_neg, integral_id]

theorem secondDerivative_zero : secondDerivative 0 = 2/3 := by
  norm_num [secondDerivative, secondDensity, variance_zero, intervalIntegral.integral_mul_const,
    integral_pow]

end
end Borwein.RadialDerivatives
