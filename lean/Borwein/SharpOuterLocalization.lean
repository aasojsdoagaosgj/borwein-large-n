import Borwein.SharpPolynomialTransfer

set_option autoImplicit false

namespace Borwein.SharpOuterLocalization
noncomputable section
open SaddleArcConnection OuterArcGeometry

theorem all_denominators (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hθ : region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  by_cases hb1 : q.den = 1
  · exact SharpPolynomialTransfer.One.polynomial_from_gap n τ θ q hn hτ hT hq hb1
      (CertifiedDenominatorOne.all_gap τ (DirichletCover.localAngle n θ q) hτ hT)
  by_cases hb5 : q.den = 5
  · exact SharpDenominatorFive.polynomial_decay n τ θ q hn hτ hT hq hb5 hθ
  by_cases hd : 5 ∣ q.den
  · obtain ⟨B,hB⟩ := hd
    have hp := q.pos
    by_cases hsmall : q.den ≤ 300
    · exact SharpPolynomialTransfer.SmallDivisible.polynomial_decay n B τ θ q hn (by omega) hB hsmall hτ hT hq
    · exact SharpPolynomialTransfer.LargeDivisible.polynomial_decay n B τ θ q hn (by omega) hB hτ hT hq
  · have hc : q.den.Coprime 5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr hd |>.symm
    by_cases hsmall : q.den ≤ 100
    · exact SharpPolynomialTransfer.SmallCoprime.polynomial_decay n τ θ q hn (by have hp := q.pos; omega) hsmall hc hτ hT hq
    · exact SharpPolynomialTransfer.LargeCoprime.polynomial_decay n τ θ q hn (by omega) hc hτ hT hq

theorem value_bound (n : ℕ) (τ θ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hθ : region n (6/5) θ) :
    OuterMassEnvelope.valueNorm n τ θ ≤ Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  obtain ⟨q,hq⟩ := DirichletCover.exists_near (θ/(2*Real.pi)) 4139 (by norm_num)
  rw [OuterCuspBounds.valueNorm_eq_point]
  exact all_denominators n τ θ q hn hτ hT hq hθ

theorem normalized_mass (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    GapIntegralBounds.mass n τ (6/5)/((radius n τ)^m*(2*Real.pi)*bulkScale n m τ) ≤
      15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-(9/10000)*(n:ℝ)) :=
  OuterMassEnvelope.normalized_mass_bound n m τ (9/10000) (by omega)
    (fun θ hθ => value_bound n τ θ hn hτ hT hθ)

theorem coefficient_error (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ (2/5) 31147+
      MiddlePolynomialIntegral.error n τ+15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-(9/10000)*(n:ℝ)) :=
  OuterMassEnvelope.coefficient_error n m τ 31147 (9/10000) (by norm_num)
    (by exact_mod_cast hn) hτ hT hs (fun θ hθ => value_bound n τ θ hn hτ hT hθ)

end
end Borwein.SharpOuterLocalization
