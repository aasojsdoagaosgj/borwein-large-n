import Borwein.SmoothedLogSeries
import Borwein.ResonantFourierSplit

set_option autoImplicit false

namespace Borwein.SmoothedLogTail
noncomputable section
open Complex MeasureTheory SmoothedLogSeries ZeroPoleBudget

def partialSum (b K : ℕ) (η : ℝ) (z : ℂ) : ℂ :=
  ∑ k ∈ (Finset.Icc 1 K).filter (fun k => b ∣ k),
    (weight η k:ℂ)*(∫ x in (0:ℝ)..1, Complex.exp (-(k:ℂ)*z*(x:ℂ)))

def tail (K : ℕ) (η : ℝ) : ℝ :=
  ((Real.exp (-η))^(K+1)/(K+1:ℕ))*(1-Real.exp (-η))⁻¹

theorem integral_filtered (b k : ℕ) (η : ℝ) (z : ℂ) :
    (∫ x in (0:ℝ)..1, filtered b η z k x) =
      if b ∣ k then (weight η k:ℂ)*(∫ x in (0:ℝ)..1, Complex.exp (-(k:ℂ)*z*(x:ℂ))) else 0 := by
  by_cases hk : b ∣ k
  · simp only [filtered,if_pos hk,term_weighted,intervalIntegral.integral_const_mul]
  · simp [filtered,hk]

theorem partial_eq_range (b K : ℕ) (η : ℝ) (z : ℂ) :
    partialSum b K η z = ∑ k ∈ Finset.range (K+1), ∫ x in (0:ℝ)..1, filtered b η z k x := by
  have he : (∑ k ∈ Finset.Icc 1 K, ∫ x in (0:ℝ)..1, filtered b η z k x) =
      ∑ k ∈ Finset.range (K+1), ∫ x in (0:ℝ)..1, filtered b η z k x := by
    apply Finset.sum_subset
    · intro k hk
      have hh := Finset.mem_Icc.mp hk
      exact Finset.mem_range.mpr (by omega)
    · intro k hk hn
      have hh := Finset.mem_range.mp hk
      have hk0 : k = 0 := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
      simp [hk0,filtered,term]
  rw [← he,partialSum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  exact (integral_filtered b k η z).symm

theorem integral_norm_bound (b k : ℕ) (η : ℝ) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖∫ x in (0:ℝ)..1, filtered b η z k x‖ ≤ weight η k := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 1) (f := filtered b η z k) (by
      intro x hx
      have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by simpa using hx
      exact norm_filtered_le b η z k x hz hx'.1.le)
  simpa using h

theorem tail_weight_bound (K j : ℕ) (η : ℝ) :
    weight η (j+(K+1)) ≤ ((Real.exp (-η))^(K+1)/(K+1:ℕ))*(Real.exp (-η))^j := by
  rw [← FiniteBlockLocalization.weight_eq]
  have hd : (0:ℝ) < (K+1:ℕ) := by positivity
  have hn : ((K+1:ℕ):ℝ) ≤ ((j+(K+1):ℕ):ℝ) := by exact_mod_cast Nat.le_add_left (K+1) j
  have h := div_le_div_of_nonneg_left (pow_nonneg (Real.exp_pos (-η)).le (j+(K+1))) hd hn
  apply h.trans_eq
  rw [pow_add]
  ring

theorem tail_integral_bound (b K : ℕ) (η : ℝ) (z : ℂ) (hη : 0 < η) (hz : 0 ≤ z.re) :
    ‖∑' j : ℕ, ∫ x in (0:ℝ)..1, filtered b η z (j+(K+1)) x‖ ≤ tail K η := by
  apply tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one (Real.exp_pos (-η)).le
      (Real.exp_lt_one_iff.mpr (by linarith))).mul_left ((Real.exp (-η))^(K+1)/(K+1:ℕ)))
  intro j
  exact (integral_norm_bound b (j+(K+1)) η z hz).trans (tail_weight_bound K j η)

theorem truncation_bound (b K : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) :
    ‖partialSum b K η z-(∫ x in (0:ℝ)..1, logValue b η z x)‖ ≤ tail K η := by
  have hs := hasSum_integral b η z hb hη hz
  rw [partial_eq_range,← hs.tsum_eq,← hs.summable.sum_add_tsum_nat_add (K+1),sub_add_cancel_left,norm_neg]
  exact tail_integral_bound b K η z hη hz

end
end Borwein.SmoothedLogTail
