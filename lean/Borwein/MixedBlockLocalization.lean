import Borwein.AbelRadialBound

namespace Borwein.MixedBlockLocalization
noncomputable section
open scoped BigOperators
open FiniteBlockLocalization (point tail blockBound)
open FiniteFourierKernel (coefficient finiteSum)
open ZeroPoleBudget (weight)

def mixedBound (n k L : ℕ) (τ θ : ℝ) :=
  if k ≤ L then blockBound n k τ θ else RadialKernelProfile.profile ((k:ℝ)*θ)+4

theorem negative_re_abel (n k : ℕ) (τ θ η : ℝ) (hτ : 0 ≤ τ)
    (hs : Real.sin ((k:ℝ)*θ/2) ≠ 0) (hs5 : Real.sin (5*((k:ℝ)*θ)/2) ≠ 0) :
    -(coefficient n k (point n τ θ) (Real.exp (-η))).re ≤
      weight η k*(RadialKernelProfile.profile ((k:ℝ)*θ)+4) := by
  rw [FiniteBlockLocalization.coefficient_re,← mul_neg]
  apply mul_le_mul_of_nonneg_left _ (by unfold weight; positivity)
  have h : -(finiteSum n ((point n τ θ)^k)).re ≤ ‖finiteSum n ((point n τ θ)^k)‖ := by
    simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-finiteSum n ((point n τ θ)^k))
  refine h.trans ?_
  rw [FiniteBlockLocalization.point_pow]
  exact AbelRadialBound.finite_sum_upper n (Real.exp (-((k:ℝ)*τ/(5*n)))) ((k:ℝ)*θ)
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) hs hs5

theorem negative_re_mixed (n : ℕ) (hn : 0 < n) (k L : ℕ) (τ θ η : ℝ) (hτ : 0 ≤ τ)
    (hs : Real.sin ((k:ℝ)*θ/2) ≠ 0) (hs5 : Real.sin (5*((k:ℝ)*θ)/2) ≠ 0) :
    -(coefficient n k (point n τ θ) (Real.exp (-η))).re ≤ weight η k*mixedBound n k L τ θ := by
  by_cases hk : k ≤ L
  · simpa only [mixedBound,if_pos hk] using FiniteBlockLocalization.negative_re_block n hn k τ θ η hτ hs hs5
  · simpa only [mixedBound,if_neg hk] using negative_re_abel n k τ θ η hτ hs hs5

theorem polynomial_log_split (n : ℕ) (hn : 0 < n) (K L : ℕ) (τ θ η : ℝ)
    (hτ : 0 ≤ τ) (hη : 0 < η) (P : ℕ → Prop) [DecidablePred P]
    (hs : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin ((k:ℝ)*θ/2) ≠ 0)
    (hs5 : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin (5*((k:ℝ)*θ)/2) ≠ 0)
    (hv : Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n) ≠ 0) :
    Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      2*η*n+(4*n)*(∑ k ∈ (Finset.Icc 1 K).filter P, weight η k)+
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ P k), weight η k*mixedBound n k L τ θ)+
      tail n K η := by
  have h := FiniteFourierKernel.polynomial_log_truncated_upper n K (point n τ θ)
    (FiniteBlockLocalization.point_norm_le n τ θ hτ) η hη hv
  rw [FiniteBlockLocalization.sum_range_eq_Icc,Complex.re_sum] at h
  have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) P
    (fun k => -(coefficient n k (point n τ θ) (Real.exp (-η))).re)
  have hr := Finset.sum_le_sum (s := (Finset.Icc 1 K).filter P) (fun k _ =>
    FiniteBlockLocalization.negative_re_coarse n k (point n τ θ) (FiniteBlockLocalization.point_norm_le n τ θ hτ) η)
  have hm := Finset.sum_le_sum (s := (Finset.Icc 1 K).filter (fun k => ¬ P k)) (fun k hk =>
    negative_re_mixed n hn k L τ θ η hτ
      (hs k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
      (hs5 k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2))
  have hh := add_le_add hr hm
  rw [he,Finset.sum_neg_distrib,← Finset.sum_mul] at hh
  unfold tail
  nlinarith

theorem polynomial_norm_split (n : ℕ) (hn : 0 < n) (K L : ℕ) (τ θ η : ℝ)
    (hτ : 0 ≤ τ) (hη : 0 < η) (P : ℕ → Prop) [DecidablePred P]
    (hs : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin ((k:ℝ)*θ/2) ≠ 0)
    (hs5 : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin (5*((k:ℝ)*θ)/2) ≠ 0) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (2*η*n+(4*n)*(∑ k ∈ (Finset.Icc 1 K).filter P, weight η k)+
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ P k), weight η k*mixedBound n k L τ θ)+
        tail n K η) := by
  by_cases hv : Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n) = 0
  · rw [hv,norm_zero]
    exact (Real.exp_pos _).le
  · exact Real.le_exp_of_log_le (polynomial_log_split n hn K L τ θ η hτ hη P hs hs5 hv)

end
end Borwein.MixedBlockLocalization

