import Borwein.RadialCorrectionEnvelope

namespace Borwein.IntervalLocalization
noncomputable section
open scoped BigOperators
open FiniteBlockLocalization (point tail)
open ZeroPoleBudget (weight)
open FiniteBlockDenominators (nominalCost radialCost)

def rate (r : Finset ℕ) (K : ℕ) (η : ℝ) : ℝ :=
  2*η+4*(∑ k ∈ r, weight η k)+
    (4*(Real.exp (-η))^(K+1)/(K+1:ℕ))*(1-Real.exp (-η))⁻¹

def coprimeVariation (q : ℚ) (Q K : ℕ) : ℝ :=
  (GeneralDenominatorVariation.multiplicity q K:ℝ)*(Real.pi^3*q.den/(30*Q)*
    (1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q)))

def divisibleVariation (q : ℚ) (B Q K : ℕ) : ℝ :=
  Real.pi^3*q.den/(30*Q*(1-(K:ℝ)/Q))*
    ((GeneralDenominatorVariation.multiplicity q K:ℝ)+(2*ResidueBlockCount.blocks K B:ℕ)/4)

def coprimeCost (q : ℚ) (Q K N : ℕ) (A T η : ℝ) : ℝ :=
  nominalCost (GeneralDenominatorVariation.nonresonant q K) q A η+
    RadialCorrectionEnvelope.cost (GeneralDenominatorVariation.nonresonant q K) q Q N A T η+
    coprimeVariation q Q K

def divisibleCost (q : ℚ) (B Q K N : ℕ) (A T η : ℝ) : ℝ :=
  nominalCost (FiveDivisibleVariation.nonresonant B K) q A η+
    RadialCorrectionEnvelope.cost (FiveDivisibleVariation.nonresonant B K) q Q N A T η+
    divisibleVariation q B Q K

theorem rate_identity (n K : ℕ) (η : ℝ) (r : Finset ℕ) :
    2*η*n+(4*n)*(∑ k ∈ r, weight η k)+tail n K η = (n:ℝ)*rate r K η := by
  unfold rate tail
  ring

theorem coprime_norm_upper (n N : ℕ) (hN : 0 < N) (hn : N ≤ n) (Q K : ℕ) (hQ : 0 < Q)
    (A τ T ξ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (hη : 0 < η)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5) (hKQ : 5*K < Q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ (2*Real.pi*ξ)) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*rate ((Finset.Icc 1 K).filter (fun k => q.den ∣ k)) K η+
        coprimeCost q Q K N A T η) := by
  have h := FiniteBlockDenominators.coprime_norm_upper n (by omega) Q K hQ τ ξ η hτ hη q hq hb5 hKQ
  have hr := RadialCorrectionEnvelope.cost_upper (GeneralDenominatorVariation.nonresonant q K)
    n N hN hn A τ T ξ η hτ hA hT Q hQ q hq
    (fun k hk => RadialCorrectionEnvelope.coprime_margins q hb5 Q K hQ hKQ k hk)
  have hm := RadialCorrectionEnvelope.nominal_cost_mono
    (GeneralDenominatorVariation.nonresonant q K) q A τ η hA
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold coprimeCost coprimeVariation
  rw [← rate_identity]
  linarith

theorem divisible_norm_upper (n N : ℕ) (hN : 0 < N) (hn : N ≤ n) (Q K : ℕ) (hQ : 0 < Q)
    (A τ T ξ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (hη : 0 < η)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B) (hKQ : K < Q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ (2*Real.pi*ξ)) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*rate ((Finset.Icc 1 K).filter (fun k => B ∣ k)) K η+
        divisibleCost q B Q K N A T η) := by
  have h := FiniteBlockDenominators.divisible_norm_upper n (by omega) Q K hQ τ ξ η hτ hη q hq B hb hKQ
  have hr := RadialCorrectionEnvelope.cost_upper (FiveDivisibleVariation.nonresonant B K)
    n N hN hn A τ T ξ η hτ hA hT Q hQ q hq
    (fun k hk => RadialCorrectionEnvelope.divisible_margins q B hb Q K hQ hKQ k hk)
  have hm := RadialCorrectionEnvelope.nominal_cost_mono
    (FiveDivisibleVariation.nonresonant B K) q A τ η hA
  apply h.trans
  apply Real.exp_le_exp.mpr
  unfold divisibleCost divisibleVariation
  rw [← rate_identity]
  linarith

end
end Borwein.IntervalLocalization
