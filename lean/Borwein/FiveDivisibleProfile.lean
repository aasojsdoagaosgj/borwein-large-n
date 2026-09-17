import Borwein.FiveDivisibleVariation

namespace Borwein.FiveDivisibleProfile
noncomputable section
open scoped BigOperators
open FiveDivisibleVariation (nonresonant)

open ResidueBlockCount (blocks)

theorem nonresonant_subset (q : ℚ) (B K : ℕ) (hb : q.den = 5*B) :
    nonresonant B K ⊆ GeneralDenominatorVariation.nonresonant q K := by
  intro k hk
  have hk' := Finset.mem_filter.mp hk
  apply Finset.mem_filter.mpr
  refine ⟨hk'.1, ?_⟩
  intro hd
  apply hk'.2
  exact dvd_trans (show B ∣ q.den by rw [hb]; exact dvd_mul_left _ _) hd

theorem zero_weighted_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B)
    (hKQ : K < Q) :
    (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k) ≤
      (GeneralDenominatorVariation.multiplicity q K:ℝ)*(Real.pi^3*q.den/(48*Q*(1-(K:ℝ)/Q))) := by
  by_cases hK : 2*K < q.den
  · have hsub : (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k) ≤
        ∑ k ∈ Finset.Icc 1 K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro k _ _
      unfold ZeroPoleBudget.weight ZeroPoleBudget.variation
      positivity
    simpa only [GeneralDenominatorVariation.multiplicity,if_pos hK,Nat.cast_one,one_mul] using
      hsub.trans (ZeroPoleBudget.weighted_sum ξ η hη Q K hQ q hq hK)
  · have hsub : (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k) ≤
        ∑ k ∈ GeneralDenominatorVariation.nonresonant q K,
          ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (nonresonant_subset q B K hb)
      intro k _ _
      unfold ZeroPoleBudget.weight ZeroPoleBudget.variation
      positivity
    simpa only [GeneralDenominatorVariation.multiplicity,if_neg hK] using
      hsub.trans (GeneralDenominatorVariation.zero_weighted_sum ξ η hη Q K hQ q hq hKQ)

theorem profile_term (ξ : ℝ) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B)
    (hKQ : K < Q) (k : ℕ) (hk : k ∈ nonresonant B K) :
    |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))| ≤
      (8/5:ℝ)*ZeroPoleBudget.variation ξ q k+
      (2/5:ℝ)*∑ j : Fin 4, ShiftedPoleBudget.variation ξ q k j := by
  have hkfilter := Finset.mem_filter.mp hk
  have hk' := Finset.mem_Icc.mp hkfilter.1
  have hkQ : k < Q := by omega
  have hnom : DirichletCover.Near (q:ℝ) Q q := ⟨hq.1, by simp; positivity⟩
  have h1 := FiveDivisibleVariation.five_sine_ne_zero (q:ℝ) Q hQ q hnom B k hb hkfilter.2 hkQ
  have h2 := FiveDivisibleVariation.five_sine_ne_zero ξ Q hQ q hq B k hb hkfilter.2 hkQ
  have he (x : ℝ) : 5*(2*Real.pi*((k:ℝ)*x))/2 = Real.pi*(5*(k:ℝ)*x) := by ring
  have hh := FivePoleCircle.profile_variation (2*Real.pi*((k:ℝ)*q))
    (2*Real.pi*((k:ℝ)*ξ)) (by rw [he]; exact h1) (by rw [he]; exact h2)
  have ha (x : ℝ) (j : Fin 4) :
      2*Real.pi*((k:ℝ)*x)+2*Real.pi*(j.val+1)/5 =
      2*Real.pi*((k:ℝ)*x+(j.val+1)/5) := by ring
  simp_rw [ha] at hh
  exact hh

theorem profile_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B)
    (hKQ : K < Q) :
    (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*
      |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))|) ≤
      Real.pi^3*q.den/(30*Q*(1-(K:ℝ)/Q))*
        ((GeneralDenominatorVariation.multiplicity q K:ℝ)+(2*blocks K B:ℕ)/4) := by
  have ht := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (profile_term ξ Q K hQ q hq B hb hKQ k hk)
    (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity))
  have he : (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*
      ((8/5:ℝ)*ZeroPoleBudget.variation ξ q k+
        (2/5:ℝ)*∑ j : Fin 4, ShiftedPoleBudget.variation ξ q k j)) =
      (8/5:ℝ)*(∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k)+
      (2/5:ℝ)*(∑ k ∈ nonresonant B K, ∑ j : Fin 4,
        ZeroPoleBudget.weight η k*ShiftedPoleBudget.variation ξ q k j) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl
    · intro k _; ring
    · intro k _; apply Finset.sum_congr rfl; intro j _; ring
  rw [he] at ht
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left (zero_weighted_sum ξ η hη Q K hQ q hq B hb hKQ)
      (by norm_num : (0:ℝ) ≤ 8/5))
    (mul_le_mul_of_nonneg_left (FiveDivisibleVariation.weighted_sum ξ η hη Q K hQ q hq B hb hKQ)
      (by norm_num : (0:ℝ) ≤ 2/5))
  refine ht.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem nominal_transfer (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B)
    (hKQ : K < Q) :
    (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))) ≤
      (∑ k ∈ nonresonant B K, ZeroPoleBudget.weight η k*
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q)))+
      Real.pi^3*q.den/(30*Q*(1-(K:ℝ)/Q))*
        ((GeneralDenominatorVariation.multiplicity q K:ℝ)+(2*blocks K B:ℕ)/4) := by
  have ht : ∀ k : ℕ,
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ)) ≤
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))+
        |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
          RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))| := by
    intro k
    linarith [neg_le_abs (RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ)))]
  have h := Finset.sum_le_sum (s := nonresonant B K) (fun k _ =>
    mul_le_mul_of_nonneg_left (ht k)
      (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity))
  simp only [mul_add,Finset.sum_add_distrib] at h
  exact h.trans (add_le_add le_rfl (profile_sum ξ η hη Q K hQ q hq B hb hKQ))

end
end Borwein.FiveDivisibleProfile

