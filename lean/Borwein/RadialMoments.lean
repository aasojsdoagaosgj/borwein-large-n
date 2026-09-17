import Borwein.PhaseIntegral
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-! Exact moment derivatives and strict positivity of the radial variance. -/

namespace Borwein.RadialMoments
noncomputable section
open scoped BigOperators
open Borwein.PhaseGap Borwein.PhaseIntegral

def moment (k : ℕ) (y : ℝ) : ℝ :=
  ∑ j : Fin 5, (j : ℝ)^k * Real.exp (-(j : ℝ)*y)

theorem moment_zero (y : ℝ) : moment 0 y = radialSum y := by simp [moment, radialSum]

theorem moment_zero_pos (y : ℝ) : 0 < moment 0 y := by
  rw [moment_zero]; exact radialDenominator_pos y

@[fun_prop]
theorem continuous_moment (k : ℕ) : Continuous (moment k) := by unfold moment; fun_prop

theorem hasDerivAt_moment (k : ℕ) (y : ℝ) :
    HasDerivAt (moment k) (-moment (k+1) y) y := by
  have hterm (j : Fin 5) :
      HasDerivAt (fun u : ℝ => (j : ℝ)^k * Real.exp (-(j : ℝ)*u))
        (-(j : ℝ)^(k+1) * Real.exp (-(j : ℝ)*y)) y := by
    apply (((hasDerivAt_id y).const_mul (-(j : ℝ))).exp.const_mul ((j : ℝ)^k)).congr_deriv
    simp only [pow_succ, id_eq]
    ring
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)
  change HasDerivAt (fun u => ∑ j : Fin 5, (j : ℝ)^k * Real.exp (-(j : ℝ)*u))
    (-moment (k+1) y) y
  simpa only [moment, Finset.sum_neg_distrib, neg_mul] using h

def mean (y : ℝ) : ℝ := moment 1 y / moment 0 y
def second (y : ℝ) : ℝ := moment 2 y / moment 0 y
def variance (y : ℝ) : ℝ := second y - mean y ^ 2

theorem mean_eq_weighted (y : ℝ) : mean y = ∑ j : Fin 5, (j : ℝ)*radialWeight y j := by
  unfold mean moment radialWeight
  simp only [pow_zero, pow_one, one_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem second_eq_weighted (y : ℝ) : second y = ∑ j : Fin 5, (j : ℝ)^2*radialWeight y j := by
  unfold second moment radialWeight
  simp only [pow_zero, one_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem mean_nonneg (y : ℝ) : 0 ≤ mean y := by
  rw [mean_eq_weighted]
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (by positivity) (radialWeight_pos y j).le

theorem mean_pos (y : ℝ) : 0 < mean y := by
  rw [mean_eq_weighted]
  apply Finset.sum_pos'
  · intro j _; exact mul_nonneg (by positivity) (radialWeight_pos y j).le
  · refine ⟨1, Finset.mem_univ _, ?_⟩
    simpa using radialWeight_pos y 1

theorem mean_le_four (y : ℝ) : mean y ≤ 4 := by
  rw [mean_eq_weighted]
  calc
    (∑ j : Fin 5, (j : ℝ)*radialWeight y j) ≤ ∑ j : Fin 5, 4*radialWeight y j := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (radialWeight_pos y j).le
      exact_mod_cast Nat.le_of_lt_succ j.isLt
    _ = 4 := by rw [← Finset.mul_sum, radialWeight_sum]; ring

theorem second_le_sixteen (y : ℝ) : second y ≤ 16 := by
  rw [second_eq_weighted]
  calc
    (∑ j : Fin 5, (j : ℝ)^2*radialWeight y j) ≤ ∑ j : Fin 5, 16*radialWeight y j := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ (radialWeight_pos y j).le
      have hj : (j : ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      have hj0 : 0 ≤ (j : ℝ) := by positivity
      nlinarith
    _ = 16 := by rw [← Finset.mul_sum, radialWeight_sum]; ring

theorem variance_eq_central (y : ℝ) :
    variance y = ∑ j : Fin 5, radialWeight y j * ((j : ℝ) - mean y)^2 := by
  symm
  calc
    (∑ j : Fin 5, radialWeight y j * ((j : ℝ) - mean y)^2) =
        (∑ j : Fin 5, (j : ℝ)^2*radialWeight y j) -
        2*mean y*(∑ j : Fin 5, (j : ℝ)*radialWeight y j) +
        mean y^2*(∑ j : Fin 5, radialWeight y j) := by
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = variance y := by
      rw [← mean_eq_weighted, ← second_eq_weighted, radialWeight_sum]
      unfold variance
      ring

theorem variance_pos (y : ℝ) : 0 < variance y := by
  rw [variance_eq_central]
  apply Finset.sum_pos'
  · intro j _; exact mul_nonneg (radialWeight_pos y j).le (sq_nonneg _)
  · by_cases hm : mean y = 0
    · refine ⟨1, Finset.mem_univ _, ?_⟩
      simpa [hm] using radialWeight_pos y 1
    · refine ⟨0, Finset.mem_univ _, ?_⟩
      simpa using mul_pos (radialWeight_pos y 0) (sq_pos_of_ne_zero hm)

theorem variance_le_sixteen (y : ℝ) : variance y ≤ 16 := by
  unfold variance
  nlinarith [second_le_sixteen y, sq_nonneg (mean y)]

@[fun_prop]
theorem continuous_mean : Continuous mean :=
  (continuous_moment 1).div (continuous_moment 0) (fun y => ne_of_gt (moment_zero_pos y))

@[fun_prop]
theorem continuous_second : Continuous second :=
  (continuous_moment 2).div (continuous_moment 0) (fun y => ne_of_gt (moment_zero_pos y))

@[fun_prop]
theorem continuous_variance : Continuous variance := continuous_second.sub (continuous_mean.pow 2)

theorem hasDerivAt_mean (y : ℝ) : HasDerivAt mean (-variance y) y := by
  have h := (hasDerivAt_moment 1 y).div (hasDerivAt_moment 0 y) (ne_of_gt (moment_zero_pos y))
  apply h.congr_deriv
  simp only [variance, second, mean, Nat.reduceAdd]
  field_simp
  ring

theorem hasDerivAt_log_radialSum (y : ℝ) :
    HasDerivAt (fun u => Real.log (radialSum u)) (-mean y) y := by
  have h := (hasDerivAt_moment 0 y).log (ne_of_gt (moment_zero_pos y))
  simpa [moment_zero, mean, neg_div] using h

theorem mean_zero : mean 0 = 2 := by norm_num [mean, moment, Fin.sum_univ_five]
theorem variance_zero : variance 0 = 2 := by
  norm_num [variance, second, mean, moment, Fin.sum_univ_five]

end
end Borwein.RadialMoments
