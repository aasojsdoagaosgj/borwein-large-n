import Borwein.OuterMassEnvelope
import Borwein.MixedIntervalLocalization

namespace Borwein.OuterCuspBounds
noncomputable section

theorem valueNorm_eq_point (n : ℕ) (τ θ : ℝ) : OuterMassEnvelope.valueNorm n τ θ =
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ)
      (Borwein.polynomial n)‖ := by
  simp only [OuterMassEnvelope.valueNorm,FiniteBlockLocalization.point,
    SaddleArcConnection.radius,AngularKernel.circle_eq_exp]

theorem coprime_bound (n N : ℕ) (hN : 0 < N) (hn : N ≤ n) (Q K L : ℕ) (hQ : 0 < Q)
    (A τ T θ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (hη : 0 < η)
    (q : ℚ) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hb5 : q.den.Coprime 5) (hKQ : 5*K < Q) :
    OuterMassEnvelope.valueNorm n τ θ ≤
      Real.exp ((n:ℝ)*IntervalLocalization.rate ((Finset.Icc 1 K).filter (fun k => q.den ∣ k)) K η+
        MixedIntervalLocalization.cost (GeneralDenominatorVariation.nonresonant q K) q Q N L A T η+
        IntervalLocalization.coprimeVariation q Q K) := by
  have h := MixedIntervalLocalization.coprime_norm_upper n N hN hn Q K L hQ A τ T
    (θ/(2*Real.pi)) η hτ hA hT hη q hq hb5 hKQ
  have he : 2*Real.pi*(θ/(2*Real.pi)) = θ := by field_simp
  rw [he] at h
  rw [valueNorm_eq_point]
  exact h

theorem divisible_bound (n N : ℕ) (hN : 0 < N) (hn : N ≤ n) (Q K L : ℕ) (hQ : 0 < Q)
    (A τ T θ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (hη : 0 < η)
    (q : ℚ) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (B : ℕ) (hb : q.den = 5*B) (hKQ : K < Q) :
    OuterMassEnvelope.valueNorm n τ θ ≤
      Real.exp ((n:ℝ)*IntervalLocalization.rate ((Finset.Icc 1 K).filter (fun k => B ∣ k)) K η+
        MixedIntervalLocalization.cost (FiveDivisibleVariation.nonresonant B K) q Q N L A T η+
        IntervalLocalization.divisibleVariation q B Q K) := by
  have h := MixedIntervalLocalization.divisible_norm_upper n N hN hn Q K L hQ A τ T
    (θ/(2*Real.pi)) η hτ hA hT hη q hq B hb hKQ
  have he : 2*Real.pi*(θ/(2*Real.pi)) = θ := by field_simp
  rw [he] at h
  rw [valueNorm_eq_point]
  exact h

end
end Borwein.OuterCuspBounds
