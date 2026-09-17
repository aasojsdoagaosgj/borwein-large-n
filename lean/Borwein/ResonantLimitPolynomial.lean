import Borwein.ResonantMainTail
import Borwein.ResonantPolynomialBound
import Borwein.OuterResonantGap

set_option autoImplicit false

namespace Borwein.ResonantLimitPolynomial
noncomputable section
open Complex ResonantMainTail ResonantArgumentBounds ExponentialKernelRemainder
  FiniteBlockLocalization ResonantFourierSplit

theorem combined_tail (n K : ℕ) (η : ℝ) :
    6*n*SmoothedLogTail.tail K η+FiniteBlockLocalization.tail n K η =
      10*n*SmoothedLogTail.tail K η := by
  unfold SmoothedLogTail.tail FiniteBlockLocalization.tail
  ring

theorem norm_upper (n N Q K c : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi)
    (hc : 0 < c) (hd : ∀ k : ℕ, q.den ∣ 5*k ↔ c ∣ k) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (n*(2*η+height q.den c η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)+
        10*SmoothedLogTail.tail K η)+‖nonresonant n K (point n τ θ) η q‖+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η)) := by
  apply (ResonantPolynomialBound.polynomial_norm_upper n N Q K τ T θ η q
    hN hn hQ hτ hT hη hη1 hq hZ).trans
  apply Real.exp_le_exp.mpr
  have hr := main_real_upper n K c τ θ η q hc hd hη hτ
  have ht := combined_tail n K η
  nlinarith

theorem coprime_norm_upper (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) (hb : q.den.Coprime 5) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (n*(2*η+(4/(q.den:ℝ))*SmoothedResonantMain.poleIntegral q.den η
        ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)+10*SmoothedLogTail.tail K η)+
        ‖nonresonant n K (point n τ θ) η q‖+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η)) := by
  have h := norm_upper n N Q K q.den τ T θ η q hN hn hQ hτ hT hη hη1 hq hZ
    q.pos (coprime_filter q.den hb)
  rwa [coprime_height q.den η _ q.pos hη (by simpa using hτ)] at h

theorem five_norm_upper (n N Q K B : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) (hB : 0 < B) (hb : q.den = 5*B) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (n*(2*η+SmoothedPhase.smoothedModulus ((B:ℝ)*η) ((B:ℝ)*τ)
        ((B:ℝ)*DirichletCover.localAngle n θ q)/(B:ℝ)+10*SmoothedLogTail.tail K η)+
        ‖nonresonant n K (point n τ θ) η q‖+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η)) := by
  have h := norm_upper n N Q K B τ T θ η q hN hn hQ hτ hT hη hη1 hq hZ hB
    (fun k => by rw [hb]; exact five_filter B k)
  rwa [hb,five_height B η τ _ hB hη hτ] at h

theorem denominator_one (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) (hb : q.den = 1) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (n*(2*η+4*SmoothedResonantMain.poleIntegral 1 η
        ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)+10*SmoothedLogTail.tail K η)+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η)) := by
  have h := coprime_norm_upper n N Q K τ T θ η q hN hn hQ hτ hT hη hη1 hq hZ
    (by simp [hb])
  rw [nonresonant_denominator_one n K (point n τ θ) η q hb,norm_zero,add_zero] at h
  simpa only [hb,Nat.cast_one,div_one] using h

theorem denominator_five_gap (n N Q K : ℕ) (τ θ : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 2 ≤ Q) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K (11/2) q < 2*Real.pi)
    (hb : q.den = 5) (hθ : OuterArcGeometry.region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (n*(PhaseIntegral.radialR τ-(31:ℝ)/3125+2*(113/40000)+
        10*SmoothedLogTail.tail K (113/40000))+
        ‖nonresonant n K (point n τ θ) (113/40000) q‖+
        4*kappa (radiusBound N Q K (11/2) q)*Real.log (2/(113/40000))) := by
  have hp := five_norm_upper n N Q K 1 τ (11/2) θ (113/40000) q hN hn (by omega)
    hτ hT (by norm_num) (by norm_num) hq hZ (by norm_num) (by simpa using hb)
  simp only [Nat.cast_one,one_mul,div_one] at hp
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hg := OuterResonantGap.denominator_five_modulus n Q τ θ (by omega) hQ hτ hT hθ q hq hb
  have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

end
end Borwein.ResonantLimitPolynomial
