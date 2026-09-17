import Borwein.LargeDivisibleCertificate
import Borwein.OuterCuspBounds

set_option autoImplicit false

namespace Borwein.CertifiedOuterLocalization
noncomputable section
open SaddleArcConnection OuterArcGeometry

theorem all_denominators (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hθ : region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  by_cases hb : 5 ∣ q.den
  · exact LargeDivisibleCertificate.all_divisible n τ θ q hn hb hτ hT hq hθ
  · have hc : q.den.Coprime 5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr hb |>.symm
    exact LargeCoprimeCertificate.all_coprime n τ θ q hn hc hτ hT hq

theorem outer_polynomial (n : ℕ) (τ θ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hθ : region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  obtain ⟨q,hq⟩ := DirichletCover.exists_near (θ/(2*Real.pi)) 4139 (by norm_num)
  exact all_denominators n τ θ q hn hτ hT hq hθ

theorem value_bound (n : ℕ) (τ θ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hθ : region n (6/5) θ) :
    OuterMassEnvelope.valueNorm n τ θ ≤ Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  rw [OuterCuspBounds.valueNorm_eq_point]
  exact outer_polynomial n τ θ hn hτ hT hθ

theorem normalized_mass (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    GapIntegralBounds.mass n τ (6/5)/((radius n τ)^m*(2*Real.pi)*bulkScale n m τ) ≤
      15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-(n:ℝ)/4000) := by
  have h := OuterMassEnvelope.normalized_mass_bound n m τ (1/4000) (by omega)
    (fun θ hθ => value_bound n τ θ hn hτ hT hθ)
  convert h using 1 <;> ring

theorem coefficient_error (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ (2/5) 31147+
      MiddlePolynomialIntegral.error n τ+15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-(n:ℝ)/4000) := by
  have h := OuterMassEnvelope.coefficient_error n m τ 31147 (1/4000) (by norm_num)
    (by exact_mod_cast hn) hτ hT hs (fun θ hθ => value_bound n τ θ hn hτ hT hθ)
  convert h using 1 <;> ring

end
end Borwein.CertifiedOuterLocalization
