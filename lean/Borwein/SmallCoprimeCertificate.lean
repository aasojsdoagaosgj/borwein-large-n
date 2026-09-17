import Borwein.CoprimeResonantGap
import Borwein.CoprimeNonresonantBound
import Borwein.SmallDivisibleCertificate
import Borwein.CertifiedDenominatorOne

set_option autoImplicit false

namespace Borwein.SmallCoprimeCertificate
noncomputable section
open ResonantArgumentBounds ExponentialKernelRemainder PositiveCuspCertificate

def coefficient (q : ℚ) : ℝ :=
  (q.den:ℝ)/(2*(1-(718:ℝ)/4139))+(q.den:ℝ)/(2*(1-5*(718:ℝ)/4139))

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den ≤ 100) :
    2*eta+10*SmoothedLogTail.tail 718 eta+
      (coefficient q+4*kappa (radiusBound 31147 4139 718 (11/2) q))*Real.log (2/eta)/(n:ℝ)
        ≤ (13/100:ℝ)-1/4000 := by
  have hb' : (q.den:ℝ) ≤ 100 := by exact_mod_cast hb
  have hc : coefficient q ≤ 440 := by unfold coefficient; norm_num; linarith
  have hk := SmallDivisibleCertificate.kappa_bound q
  have hl := DenominatorOnePositiveCertificate.log_bound
  have hl0 : 0 ≤ Real.log (2/eta) := Real.log_nonneg (by norm_num [eta])
  have hm : (coefficient q+4*kappa (radiusBound 31147 4139 718 (11/2) q))*Real.log (2/eta) ≤ 2712 := by
    have hmul := mul_le_mul_of_nonneg_right (show
      coefficient q+4*kappa (radiusBound 31147 4139 718 (11/2) q) ≤ 452 by linarith) hl0
    nlinarith
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hd := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)
  have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2712) (by norm_num : (0:ℝ) < 31147) hn'
  have ht := DenominatorOnePositiveCertificate.tail_bound
  norm_num [eta] at *
  linarith

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hbmin : 2 ≤ q.den) (hbmax : q.den ≤ 100) (hb : q.den.Coprime 5)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  have hp := ResonantLimitPolynomial.coprime_norm_upper n 31147 4139 718 τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) hτ hT (by norm_num [eta]) (by norm_num [eta]) hq
    ((SmallDivisibleCertificate.radius_bound q).trans_lt (by linarith [Real.pi_gt_three])) hb
  have hg := CoprimeResonantGap.uniform_gap q.den eta τ (DirichletCover.localAngle n θ q)
    hbmin (by norm_num [eta]) hτ hT
  have hs := CoprimeNonresonantBound.nonresonant_bound n 4139 718 τ θ eta q
    (by norm_num) (by norm_num) hτ (by norm_num [eta]) (by norm_num [eta]) hq
  change _ ≤ coefficient q*Real.log (2/eta) at hs
  have hbgt := budget n q hn hbmax
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (coefficient q+4*kappa (radiusBound 31147 4139 718 (11/2) q))*Real.log (2/eta)/(n:ℝ) ≤
      (13/100:ℝ)-1/4000-2*eta-10*SmoothedLogTail.tail 718 eta by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem all_small (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hbmax : q.den ≤ 100) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q)
    (hθ : OuterArcGeometry.region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  by_cases hb1 : q.den = 1
  · exact CertifiedDenominatorOne.polynomial_decay n τ θ q hn hτ hT hq hb1
  by_cases hb5 : 5 ∣ q.den
  · exact SmallDivisibleCertificate.all_small_five n τ θ q hn hb5 (by omega) hτ hT hq hθ
  have hc : q.den.Coprime 5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 5)).mpr hb5 |>.symm
  exact polynomial_decay n τ θ q hn (by have hp := q.pos; omega) hbmax hc hτ hT hq

end
end Borwein.SmallCoprimeCertificate
