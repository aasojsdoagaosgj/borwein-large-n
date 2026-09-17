import Borwein.MixedBlockLocalization

namespace Borwein.MixedIntervalLocalization
noncomputable section
open scoped BigOperators
open FiniteBlockLocalization (point tail blockBound)
open MixedBlockLocalization (mixedBound)
open ZeroPoleBudget (weight)
open RadialKernelProfile (profile)

def headSet (s : Finset ℕ) (L : ℕ) := s.filter (fun k => k ≤ L)
def tailSet (s : Finset ℕ) (L : ℕ) := s.filter (fun k => ¬ k ≤ L)

def cost (s : Finset ℕ) (q : ℚ) (Q N L : ℕ) (A T η : ℝ) :=
  FiniteBlockDenominators.nominalCost (headSet s L) q A η+
    (∑ k ∈ tailSet s L, weight η k*profile (2*Real.pi*((k:ℝ)*q)))+
    RadialCorrectionEnvelope.cost (headSet s L) q Q N A T η+
    4*(∑ k ∈ tailSet s L, weight η k)

theorem sum_upper (s : Finset ℕ) (n N L : ℕ) (hN : 0 < N) (hn : N ≤ n)
    (A τ T ξ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T)
    (Q : ℕ) (hQ : 0 < Q) (q : ℚ) (hq : DirichletCover.Near ξ Q q)
    (hm : ∀ k ∈ s, 0 < RadialCorrectionEnvelope.margin q Q k ∧
      0 < RadialCorrectionEnvelope.margin q Q (5*k)) :
    (∑ k ∈ s, weight η k*mixedBound n k L τ (2*Real.pi*ξ)) ≤
      cost s q Q N L A T η+
      ∑ k ∈ s, weight η k*|profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
  let p := headSet s L
  let r := tailSet s L
  have hp := FiniteBlockDenominators.sum_block_transfer p n τ ξ η hτ q
  have hrad := RadialCorrectionEnvelope.cost_upper p n N hN hn A τ T ξ η hτ hA hT Q hQ q hq
    (fun k hk => hm k (Finset.mem_filter.mp hk).1)
  have hnom := RadialCorrectionEnvelope.nominal_cost_mono p q A τ η hA
  have hp' : (∑ k ∈ p, weight η k*blockBound n k τ (2*Real.pi*ξ)) ≤
      FiniteBlockDenominators.nominalCost p q A η+RadialCorrectionEnvelope.cost p q Q N A T η+
      ∑ k ∈ p, weight η k*|profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
    linarith
  have hr : (∑ k ∈ r, weight η k*(profile ((k:ℝ)*(2*Real.pi*ξ))+4)) ≤
      (∑ k ∈ r, weight η k*profile (2*Real.pi*((k:ℝ)*q)))+4*(∑ k ∈ r, weight η k)+
      ∑ k ∈ r, weight η k*|profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
    have ht (k : ℕ) : weight η k*(profile ((k:ℝ)*(2*Real.pi*ξ))+4) ≤
        weight η k*profile (2*Real.pi*((k:ℝ)*q))+4*weight η k+
        weight η k*|profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
      have hh := neg_le_abs (profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ)))
      have hv : profile (2*Real.pi*((k:ℝ)*ξ)) ≤ profile (2*Real.pi*((k:ℝ)*q))+
          |profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by linarith
      have hw := mul_le_mul_of_nonneg_left hv (show 0 ≤ weight η k by unfold weight; positivity)
      rw [show (k:ℝ)*(2*Real.pi*ξ) = 2*Real.pi*((k:ℝ)*ξ) by ring]
      nlinarith
    have hh := Finset.sum_le_sum (s := r) (fun k _ => ht k)
    simpa only [Finset.sum_add_distrib,← Finset.mul_sum] using hh
  have hpEq : (∑ k ∈ p, weight η k*mixedBound n k L τ (2*Real.pi*ξ)) =
      ∑ k ∈ p, weight η k*blockBound n k τ (2*Real.pi*ξ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mixedBound,if_pos (Finset.mem_filter.mp hk).2]
  have hrEq : (∑ k ∈ r, weight η k*mixedBound n k L τ (2*Real.pi*ξ)) =
      ∑ k ∈ r, weight η k*(profile ((k:ℝ)*(2*Real.pi*ξ))+4) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [mixedBound,if_neg (Finset.mem_filter.mp hk).2]
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun k => k ≤ L)
    (fun k => weight η k*mixedBound n k L τ (2*Real.pi*ξ))
  change (∑ k ∈ p, _) + (∑ k ∈ r, _) = _ at hsplit
  rw [hpEq,hrEq] at hsplit
  have hvsplit := Finset.sum_filter_add_sum_filter_not s (fun k => k ≤ L)
    (fun k => weight η k*|profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))|)
  change (∑ k ∈ p, _) + (∑ k ∈ r, _) = _ at hvsplit
  unfold cost
  change _ ≤ FiniteBlockDenominators.nominalCost p q A η+
    (∑ k ∈ r, weight η k*profile (2*Real.pi*((k:ℝ)*q)))+
    RadialCorrectionEnvelope.cost p q Q N A T η+4*(∑ k ∈ r, weight η k)+_
  linarith

theorem coprime_norm_upper (n N : ℕ) (hN : 0 < N) (hn : N ≤ n) (Q K L : ℕ) (hQ : 0 < Q)
    (A τ T ξ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (hη : 0 < η)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5) (hKQ : 5*K < Q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ (2*Real.pi*ξ)) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*IntervalLocalization.rate ((Finset.Icc 1 K).filter (fun k => q.den ∣ k)) K η+
        cost (GeneralDenominatorVariation.nonresonant q K) q Q N L A T η+
        IntervalLocalization.coprimeVariation q Q K) := by
  have hs := FiniteBlockDenominators.coprime_sines ξ Q K hQ q hq hb5 hKQ
  have h := MixedBlockLocalization.polynomial_norm_split n (by omega) K L τ (2*Real.pi*ξ) η hτ hη
    (fun k => q.den ∣ k) (fun k hk hkn => (hs k hk hkn).1) (fun k hk hkn => (hs k hk hkn).2)
  have ht := (sum_upper (GeneralDenominatorVariation.nonresonant q K) n N L hN hn A τ T ξ η hτ hA hT
    Q hQ q hq (fun k hk => RadialCorrectionEnvelope.coprime_margins q hb5 Q K hQ hKQ k hk)).trans
    (add_le_add le_rfl (GeneralDenominatorVariation.unified_profile_sum ξ η hη.le Q K hQ q hq hb5 hKQ))
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold IntervalLocalization.coprimeVariation
  rw [← IntervalLocalization.rate_identity]
  dsimp [GeneralDenominatorVariation.nonresonant] at ht ⊢
  linarith

theorem divisible_norm_upper (n N : ℕ) (hN : 0 < N) (hn : N ≤ n) (Q K L : ℕ) (hQ : 0 < Q)
    (A τ T ξ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (hη : 0 < η)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B) (hKQ : K < Q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ (2*Real.pi*ξ)) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*IntervalLocalization.rate ((Finset.Icc 1 K).filter (fun k => B ∣ k)) K η+
        cost (FiveDivisibleVariation.nonresonant B K) q Q N L A T η+
        IntervalLocalization.divisibleVariation q B Q K) := by
  have hs := FiniteBlockDenominators.divisible_sines ξ Q K hQ q hq B hb hKQ
  have h := MixedBlockLocalization.polynomial_norm_split n (by omega) K L τ (2*Real.pi*ξ) η hτ hη
    (fun k => B ∣ k) (fun k hk hkn => (hs k hk hkn).1) (fun k hk hkn => (hs k hk hkn).2)
  have ht := (sum_upper (FiveDivisibleVariation.nonresonant B K) n N L hN hn A τ T ξ η hτ hA hT
    Q hQ q hq (fun k hk => RadialCorrectionEnvelope.divisible_margins q B hb Q K hQ hKQ k hk)).trans
    (add_le_add le_rfl (FiveDivisibleProfile.profile_sum ξ η hη.le Q K hQ q hq B hb hKQ))
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold IntervalLocalization.divisibleVariation
  rw [← IntervalLocalization.rate_identity]
  dsimp [FiveDivisibleVariation.nonresonant] at ht ⊢
  linarith

end
end Borwein.MixedIntervalLocalization

