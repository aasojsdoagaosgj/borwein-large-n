import Borwein.VarianceInterval
import Borwein.ActualPhaseTaylor

set_option autoImplicit false

namespace Borwein.MomentIntegralTable
noncomputable section
open RadialMoments ActualPhaseTaylor

def powerMass (k : ℕ) (a b : ℝ) : ℝ := (b^(k+1)-a^(k+1))/((k:ℝ)+1)
def cellIntegral (k : ℕ) (τ a b : ℝ) : ℝ := ∫ x in a..b, x^k*variance (τ*x)
def grid (m i : ℕ) : ℝ := (i:ℝ)/(m:ℝ)
def certificate (k m : ℕ) (L : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, L i*powerMass k (grid m i) (grid m (i+1))

theorem integral_power (k : ℕ) (a b : ℝ) :
    (∫ x in a..b, x^k) = powerMass k a b := by
  rw [integral_pow]
  rfl

theorem cell_enclosure (k : ℕ) (τ a b L U : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hcell : ∀ x ∈ Set.Icc a b, L ≤ variance (τ*x) ∧ variance (τ*x) ≤ U) :
    L*powerMass k a b ≤ cellIntegral k τ a b ∧
      cellIntegral k τ a b ≤ U*powerMass k a b := by
  have hc : Continuous (fun x : ℝ => x^k*variance (τ*x)) := by fun_prop
  have hL := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    ((by fun_prop : Continuous (fun x : ℝ => L*x^k)).intervalIntegrable a b)
    (hc.intervalIntegrable a b) (fun x hx => show L*x^k ≤ x^k*variance (τ*x) from by
      have h := mul_le_mul_of_nonneg_right (hcell x hx).1 (pow_nonneg (ha.trans hx.1) k)
      simpa only [mul_comm] using h)
  have hU := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab
    (hc.intervalIntegrable a b)
    ((by fun_prop : Continuous (fun x : ℝ => U*x^k)).intervalIntegrable a b)
    (fun x hx => show x^k*variance (τ*x) ≤ U*x^k from by
      have h := mul_le_mul_of_nonneg_right (hcell x hx).2 (pow_nonneg (ha.trans hx.1) k)
      simpa only [mul_comm] using h)
  rw [intervalIntegral.integral_const_mul,integral_power] at hL hU
  exact ⟨hL,hU⟩

theorem grid_mono (m : ℕ) : Monotone (grid m) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (by exact_mod_cast hij) (Nat.cast_nonneg m)

theorem integral_partition (k m : ℕ) (hm : 0 < m) (τ : ℝ) :
    (∑ i ∈ Finset.range m, cellIntegral k τ (grid m i) (grid m (i+1))) = W k τ := by
  have hc : Continuous (fun x : ℝ => x^k*variance (τ*x)) := by fun_prop
  unfold cellIntegral
  rw [intervalIntegral.sum_integral_adjacent_intervals
    (fun i (_ : i < m) => hc.intervalIntegrable (grid m i) (grid m (i+1)))]
  simp only [grid,Nat.cast_zero,zero_div,div_self (show (m:ℝ) ≠ 0 by exact_mod_cast hm.ne')]
  rfl

theorem certificate_enclosure (k m : ℕ) (hm : 0 < m) (τ : ℝ) (L U : ℕ → ℝ)
    (hcell : ∀ i < m, ∀ x ∈ Set.Icc (grid m i) (grid m (i+1)),
      L i ≤ variance (τ*x) ∧ variance (τ*x) ≤ U i) :
    certificate k m L ≤ W k τ ∧ W k τ ≤ certificate k m U := by
  have h (i : ℕ) (hi : i < m) := cell_enclosure k τ (grid m i) (grid m (i+1)) (L i) (U i)
    (by unfold grid; positivity) (grid_mono m (Nat.le_succ i)) (hcell i hi)
  have hL := Finset.sum_le_sum (fun i hi => (h i (Finset.mem_range.mp hi)).1)
  have hU := Finset.sum_le_sum (fun i hi => (h i (Finset.mem_range.mp hi)).2)
  rw [integral_partition k m hm τ] at hL hU
  exact ⟨hL,hU⟩

theorem rectangle_certificate (k m : ℕ) (hm : 0 < m) (A B τ : ℝ)
    (hA : 0 ≤ A) (hAτ : A ≤ τ) (hτB : τ ≤ B) (l u L U : ℕ → ℝ)
    (hl0 : ∀ i < m, 0 ≤ l i)
    (hl : ∀ i < m, l i ≤ Real.exp (-B*grid m (i+1)))
    (hu : ∀ i < m, Real.exp (-A*grid m i) ≤ u i)
    (hL : ∀ i < m, L i ≤ VarianceInterval.numerator (l i)/GroupedWeights.denominator (u i)^2)
    (hU : ∀ i < m, VarianceInterval.numerator (u i)/GroupedWeights.denominator (l i)^2 ≤ U i) :
    certificate k m L ≤ W k τ ∧ W k τ ≤ certificate k m U := by
  apply certificate_enclosure k m hm τ L U
  intro i hi x hx
  have h := VarianceInterval.rectangle_variance A B τ (grid m i) (grid m (i+1)) x (l i) (u i)
    hA hAτ hτB (by unfold grid; positivity) hx.1 hx.2 (hl0 i hi) (hl i hi) (hu i hi)
  exact ⟨(hL i hi).trans h.1,h.2.trans (hU i hi)⟩

theorem grid_powerMass (k m i : ℕ) :
    powerMass k (grid m i) (grid m (i+1)) =
      (((i:ℝ)+1)^(k+1)-(i:ℝ)^(k+1))/(((k:ℝ)+1)*(m:ℝ)^(k+1)) := by
  unfold powerMass grid
  rw [Nat.cast_add,Nat.cast_one,div_pow,div_pow]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end Borwein.MomentIntegralTable
