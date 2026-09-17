import Borwein.SincBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Borwein.StaircaseGap
noncomputable section
open scoped BigOperators
open Borwein.SincBounds

theorem integral_one_sub_cos (t b : ℝ) :
    (∫ x in (0:ℝ)..b, (1-Real.cos (t*x))) = b*(1-Real.sinc (t*b)) := by
  by_cases ht : t = 0
  · simp [ht]
  by_cases hb : b = 0
  · simp [hb]
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    ((show Continuous (fun x : ℝ => Real.cos (t*x)) by fun_prop).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const]
  have hc := intervalIntegral.mul_integral_comp_mul_left (a := (0:ℝ)) (b := b)
    (f := Real.cos) t
  simp only [mul_zero, integral_cos, Real.sin_zero, sub_zero] at hc
  rw [Real.sinc_of_ne_zero (mul_ne_zero ht hb)]
  simp only [sub_zero, smul_eq_mul, mul_one]
  field_simp
  rw [mul_comm b t]
  nlinarith [hc]

theorem integral_cell (t a b : ℝ) :
    (∫ x in a..b, (1-Real.cos (t*x))) =
      b*(1-Real.sinc (t*b))-a*(1-Real.sinc (t*a)) := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (a := (0:ℝ)) (b := a) (c := b) (μ := MeasureTheory.volume)
    (f := fun x => 1-Real.cos (t*x))
    ((show Continuous (fun x : ℝ => 1-Real.cos (t*x)) by fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun x : ℝ => 1-Real.cos (t*x)) by fun_prop).intervalIntegrable _ _)
  rw [integral_one_sub_cos, integral_one_sub_cos] at h
  linarith

theorem summation_by_parts (g F : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, g i*(F (i+1)-F i)) =
      (∑ i ∈ Finset.range n, (g i-g (i+1))*F (i+1)) + g n*F n-g 0*F 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem staircase_identity (g b : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (hg : g n = 0) (hb : b 0 = 0) :
    (∑ i ∈ Finset.range n, g i * ∫ x in b i..b (i+1), (1-Real.cos (t*x))) =
      ∑ i ∈ Finset.range n, (g i-g (i+1))*b (i+1)*(1-Real.sinc (t*b (i+1))) := by
  simp_rw [integral_cell]
  rw [summation_by_parts g (fun i => b i*(1-Real.sinc (t*b i))) n]
  simp only [hg, hb, zero_mul, mul_zero, sub_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem staircase_lower (g b : ℕ → ℝ) (n : ℕ) (t c : ℝ)
    (hg : g n = 0) (hb : b 0 = 0)
    (hdec : ∀ i < n, g (i+1) ≤ g i)
    (hpos : ∀ i < n, 0 ≤ b (i+1))
    (hc : 0 ≤ c) (ht : c ≤ |t|) :
    (∑ i ∈ Finset.range n, (g i-g (i+1))*b (i+1)*profile (min 2 (c*b (i+1)))) ≤
      ∑ i ∈ Finset.range n, g i * ∫ x in b i..b (i+1), (1-Real.cos (t*x)) := by
  rw [staircase_identity g b n t hg hb]
  apply Finset.sum_le_sum
  intro i hi
  have hin := Finset.mem_range.mp hi
  have hp := hpos i hin
  apply mul_le_mul_of_nonneg_left
  · apply global_lower
    · exact le_min (by norm_num) (mul_nonneg hc hp)
    · exact min_le_left _ _
    · rw [abs_mul, abs_of_nonneg hp]
      exact le_trans (min_le_right _ _) (mul_le_mul_of_nonneg_right ht hp)
  · exact mul_nonneg (sub_nonneg.mpr (hdec i hin)) hp

end
end Borwein.StaircaseGap
