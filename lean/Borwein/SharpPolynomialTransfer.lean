import Borwein.SharpSharedBudgets
import Borwein.SharpDenominatorFive

set_option autoImplicit false

namespace Borwein.SharpPolynomialTransfer
noncomputable section
open PositiveCuspCertificate ResonantArgumentBounds ExponentialKernelRemainder

namespace One
open SmallAngleIntegral

open Complex SmoothedResonantMain

theorem polynomial_from_gap (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1)
    (hgap : (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 PositiveCuspCertificate.eta
      ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  have hp := ResonantLimitPolynomial.denominator_one n 31147 4139 718 τ (11/2) θ PositiveCuspCertificate.eta q
    (by norm_num) hn (by norm_num) hτ0 hτ1 (by norm_num [PositiveCuspCertificate.eta])
    (by norm_num [PositiveCuspCertificate.eta]) hq
    ((DenominatorOnePositiveCertificate.radius_bound q hb).trans_lt (by linarith [Real.pi_gt_three])) hb
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hbgt := SharpSharedBudgets.One.budget n q hn hb
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    4*ExponentialKernelRemainder.kappa (ResonantArgumentBounds.radiusBound 31147 4139 718 (11/2) q)*
      Real.log (2/PositiveCuspCertificate.eta)/(n:ℝ) ≤
      (1/40:ℝ)-9/10000-2*PositiveCuspCertificate.eta-10*SmoothedLogTail.tail 718 PositiveCuspCertificate.eta by linarith)
  nlinarith
end One

namespace SmallCoprime
open SmallCoprimeCertificate

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hbmin : 2 ≤ q.den) (hbmax : q.den ≤ 100) (hb : q.den.Coprime 5)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  have hp := ResonantLimitPolynomial.coprime_norm_upper n 31147 4139 718 τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) hτ hT (by norm_num [eta]) (by norm_num [eta]) hq
    ((SmallDivisibleCertificate.radius_bound q).trans_lt (by linarith [Real.pi_gt_three])) hb
  have hg := CoprimeResonantGap.uniform_gap q.den eta τ (DirichletCover.localAngle n θ q)
    hbmin (by norm_num [eta]) hτ hT
  have hs := CoprimeNonresonantBound.nonresonant_bound n 4139 718 τ θ eta q
    (by norm_num) (by norm_num) hτ (by norm_num [eta]) (by norm_num [eta]) hq
  change _ ≤ coefficient q*Real.log (2/eta) at hs
  have hbgt := SharpSharedBudgets.SmallCoprime.budget n q hn hbmax
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (coefficient q+4*kappa (radiusBound 31147 4139 718 (11/2) q))*Real.log (2/eta)/(n:ℝ) ≤
      (13/100:ℝ)-9/10000-2*eta-10*SmoothedLogTail.tail 718 eta by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith
end SmallCoprime

namespace SmallDivisible
open SmallDivisibleCertificate

theorem polynomial_decay (n B : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hB : 2 ≤ B) (hb : q.den = 5*B) (hbmax : q.den ≤ 300)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  have hp := ResonantLimitPolynomial.five_norm_upper n 31147 4139 718 B τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) hτ hT (by norm_num [eta]) (by norm_num [eta]) hq
    ((radius_bound q).trans_lt (by linarith [Real.pi_gt_three])) (by omega) hb
  have hg := DivisibleResonantGap.scaled_gap B eta τ (DirichletCover.localAngle n θ q)
    hB (by norm_num [eta]) hτ hT
  have hs := DivisibleNonresonantBound.nonresonant_bound n 4139 718 B τ θ eta q
    (by norm_num) (by norm_num) hτ (by norm_num [eta]) (by norm_num [eta]) hq hb
  have hbgt := SharpSharedBudgets.SmallDivisible.budget n q hn hbmax
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139))+4*kappa (radiusBound 31147 4139 718 (11/2) q))*
      Real.log (2/eta)/(n:ℝ) ≤ (119/1000:ℝ)-9/10000-2*eta-10*SmoothedLogTail.tail 718 eta by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith
end SmallDivisible

namespace LargeCoprime
open LargeCoprimeCertificate

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hb : 101 ≤ q.den) (hc : q.den.Coprime 5)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  have hp := ResonantLimitPolynomial.coprime_norm_upper n 31147 4139 718 τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) hτ hT (by norm_num [eta]) (by norm_num [eta]) hq
    ((radius_bound q hb).trans_lt (by linarith [Real.pi_gt_three])) hc
  have hM := UniformPoleBound.half_upper (q.den*eta) (q.den*τ) (q.den*DirichletCover.localAngle n θ q)
    (mul_pos (Nat.cast_pos.mpr q.pos) (by norm_num [eta])) (by positivity)
  rw [← UniformPoleBound.pole_scale] at hM
  have hmain := mul_le_mul_of_nonneg_left hM (by positivity : (0:ℝ) ≤ 4/(q.den:ℝ))
  rw [show (4/(q.den:ℝ))*(1/2) = 2/(q.den:ℝ) by ring] at hmain
  have hs := ResidueGeometricBound.nonresonant_bound n 4139 718 τ θ eta q
    (by norm_num) (by norm_num) hτ (by norm_num [eta]) hq hc
  change _ ≤ cost q at hs
  have hg := DivisibleResonantGap.radial_lower τ hT
  have hbgt := SharpSharedBudgets.LargeCoprime.budget n q hn hb hq.1
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ) ≤
      (119/500:ℝ)-9/10000-2*eta-10*SmoothedLogTail.tail 718 eta-2/(q.den:ℝ) by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith
end LargeCoprime

namespace LargeDivisible
open LargeDivisibleCertificate

theorem polynomial_decay (n B : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hB : 61 ≤ B) (hb : q.den = 5*B)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  have hp := ResonantLimitPolynomial.five_norm_upper n 31147 4139 718 B τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) hτ hT (by norm_num [eta]) (by norm_num [eta]) hq
    ((LargeCoprimeCertificate.radius_bound q (by omega)).trans_lt (by linarith [Real.pi_gt_three])) (by omega) hb
  have hM := modulus_upper (B*eta) (B*τ) (B*DirichletCover.localAngle n θ q)
    (mul_nonneg (Nat.cast_nonneg B) (by norm_num [eta])) (by positivity)
  have hmain := div_le_div_of_nonneg_right hM (Nat.cast_nonneg B)
  have hs := LargeDivisibleNonresonant.nonresonant_bound n 4139 718 B τ θ eta q
    (by norm_num) (by norm_num) hτ (by norm_num [eta]) hq hb
  change _ ≤ cost q at hs
  have hg := DivisibleResonantGap.radial_lower τ hT
  have hbgt := SharpSharedBudgets.LargeDivisible.budget n B q hn hB hb hq.1
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ) ≤
      (119/500:ℝ)-9/10000-2*eta-10*SmoothedLogTail.tail 718 eta-2/(B:ℝ) by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith
end LargeDivisible

end
end Borwein.SharpPolynomialTransfer
