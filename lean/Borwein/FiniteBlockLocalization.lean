import Borwein.FiveDivisibleProfile

namespace Borwein.FiniteBlockLocalization
noncomputable section
open scoped BigOperators
open AngularKernel (circle)
open FiniteFourierKernel (coefficient finiteSum)
open ZeroPoleBudget (weight)

def point (n : ℕ) (τ θ : ℝ) : ℂ := (Real.exp (-τ/(5*n)):ℂ)*circle θ

def blockBound (n k : ℕ) (τ θ : ℝ) : ℝ :=
  (1+Real.exp (-(k:ℝ)*τ))*(RadialKernelProfile.profile ((k:ℝ)*θ)/2+
    Real.sinh (2*((k:ℝ)*τ/(5*n)))/
      (2*|Real.sin ((k:ℝ)*θ/2)| * |Real.sin (5*((k:ℝ)*θ)/2)|))

def tail (n K : ℕ) (η : ℝ) : ℝ :=
  (4*n*(Real.exp (-η))^(K+1)/(K+1:ℕ))*(1-Real.exp (-η))⁻¹

theorem point_norm_le (n : ℕ) (τ θ : ℝ) (hτ : 0 ≤ τ) : ‖point n τ θ‖ ≤ 1 := by
  unfold point
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,
    AngularKernel.circle_norm,mul_one]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hτ) (by positivity)

theorem point_pow (n k : ℕ) (τ θ : ℝ) :
    (point n τ θ)^k = (Real.exp (-((k:ℝ)*τ/(5*n))):ℂ)*circle ((k:ℝ)*θ) := by
  unfold point
  rw [AngularKernel.radial_pow,← Real.exp_nat_mul]
  congr 3
  ring

theorem weight_eq (η : ℝ) (k : ℕ) : (Real.exp (-η))^k/(k:ℝ) = weight η k := by
  rw [← Real.exp_nat_mul]
  unfold weight
  congr 2
  ring

theorem coefficient_re (n k : ℕ) (z : ℂ) (η : ℝ) :
    (coefficient n k z (Real.exp (-η))).re = weight η k*(finiteSum n (z^k)).re := by
  unfold coefficient
  have hc : (Real.exp (-η):ℂ)^k/(k:ℂ) = ((weight η k:ℝ):ℂ) := by
    rw [← Complex.ofReal_pow,← Complex.ofReal_natCast,← Complex.ofReal_div,weight_eq]
  rw [hc,Complex.re_ofReal_mul]

theorem finite_block_bound (n : ℕ) (hn : 0 < n) (k : ℕ) (τ θ : ℝ) (hτ : 0 ≤ τ)
    (hs : Real.sin ((k:ℝ)*θ/2) ≠ 0) (hs5 : Real.sin (5*((k:ℝ)*θ)/2) ≠ 0) :
    ‖finiteSum n ((point n τ θ)^k)‖ ≤ blockBound n k τ θ := by
  rw [point_pow]
  have h := RadialKernelProfile.exponential_finite_upper n ((k:ℝ)*τ/(5*n)) ((k:ℝ)*θ)
    (by positivity) hs hs5
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (Real.exp (-((k:ℝ)*τ/(5*n))))^(5*n) = Real.exp (-(k:ℝ)*τ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [he] at h
  exact h

theorem negative_re_block (n : ℕ) (hn : 0 < n) (k : ℕ) (τ θ η : ℝ) (hτ : 0 ≤ τ)
    (hs : Real.sin ((k:ℝ)*θ/2) ≠ 0) (hs5 : Real.sin (5*((k:ℝ)*θ)/2) ≠ 0) :
    -(coefficient n k (point n τ θ) (Real.exp (-η))).re ≤ weight η k*blockBound n k τ θ := by
  rw [coefficient_re,← mul_neg]
  apply mul_le_mul_of_nonneg_left _ (by unfold weight; positivity)
  have h : -(finiteSum n ((point n τ θ)^k)).re ≤ ‖finiteSum n ((point n τ θ)^k)‖ := by
    simpa only [Complex.neg_re,norm_neg] using Complex.re_le_norm (-finiteSum n ((point n τ θ)^k))
  exact h.trans (finite_block_bound n hn k τ θ hτ hs hs5)

theorem negative_re_coarse (n k : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (η : ℝ) :
    -(coefficient n k z (Real.exp (-η))).re ≤ weight η k*(4*n) := by
  have h := (Complex.re_le_norm (-coefficient n k z (Real.exp (-η)))).trans
    (by simpa only [norm_neg] using
      FiniteFourierKernel.coefficient_norm_le n k z hz (Real.exp (-η)) (Real.exp_pos _).le)
  simpa only [Complex.neg_re,weight_eq] using h

theorem sum_range_eq_Icc (n K : ℕ) (z : ℂ) (r : ℝ) :
    (∑ k ∈ Finset.range (K+1), coefficient n k z r) =
      ∑ k ∈ Finset.Icc 1 K, coefficient n k z r := by
  symm
  apply Finset.sum_subset
  · intro k hk
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_range.mpr (by omega)
  · intro k hk hn
    have hk' := Finset.mem_range.mp hk
    have hk0 : k = 0 := by
      by_contra h
      exact hn (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    simp [hk0,coefficient]

theorem polynomial_log_split (n : ℕ) (hn : 0 < n) (K : ℕ) (τ θ η : ℝ)
    (hτ : 0 ≤ τ) (hη : 0 < η) (P : ℕ → Prop) [DecidablePred P]
    (hs : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin ((k:ℝ)*θ/2) ≠ 0)
    (hs5 : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin (5*((k:ℝ)*θ)/2) ≠ 0)
    (hv : Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n) ≠ 0) :
    Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      2*η*n+(4*n)*(∑ k ∈ (Finset.Icc 1 K).filter P, weight η k)+
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ P k), weight η k*blockBound n k τ θ)+
      tail n K η := by
  have h := FiniteFourierKernel.polynomial_log_truncated_upper n K (point n τ θ)
    (point_norm_le n τ θ hτ) η hη hv
  rw [sum_range_eq_Icc,Complex.re_sum] at h
  have he := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) P
    (fun k => -(coefficient n k (point n τ θ) (Real.exp (-η))).re)
  have hr := Finset.sum_le_sum (s := (Finset.Icc 1 K).filter P) (fun k _ =>
    negative_re_coarse n k (point n τ θ) (point_norm_le n τ θ hτ) η)
  have hm := Finset.sum_le_sum (s := (Finset.Icc 1 K).filter (fun k => ¬ P k)) (fun k hk =>
    negative_re_block n hn k τ θ η hτ
      (hs k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2)
      (hs5 k (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hk).2))
  have hh := add_le_add hr hm
  rw [he,Finset.sum_neg_distrib,← Finset.sum_mul] at hh
  unfold tail
  nlinarith

theorem polynomial_norm_split (n : ℕ) (hn : 0 < n) (K : ℕ) (τ θ η : ℝ)
    (hτ : 0 ≤ τ) (hη : 0 < η) (P : ℕ → Prop) [DecidablePred P]
    (hs : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin ((k:ℝ)*θ/2) ≠ 0)
    (hs5 : ∀ k ∈ Finset.Icc 1 K, ¬ P k → Real.sin (5*((k:ℝ)*θ)/2) ≠ 0) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (2*η*n+(4*n)*(∑ k ∈ (Finset.Icc 1 K).filter P, weight η k)+
        (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ P k), weight η k*blockBound n k τ θ)+
        tail n K η) := by
  by_cases hv : Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n) = 0
  · rw [hv,norm_zero]
    exact (Real.exp_pos _).le
  · exact Real.le_exp_of_log_le (polynomial_log_split n hn K τ θ η hτ hη P hs hs5 hv)

end
end Borwein.FiniteBlockLocalization
