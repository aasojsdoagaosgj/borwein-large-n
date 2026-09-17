import Borwein.DivisibleResonantGap
import Borwein.DivisibleNonresonantBound
import Borwein.DenominatorOnePositiveCertificate
import Borwein.DenominatorFiveCertificate

set_option autoImplicit false

namespace Borwein.SmallDivisibleCertificate
noncomputable section
open ResonantArgumentBounds ExponentialKernelRemainder PositiveCuspCertificate

theorem radius_bound (q : ℚ) : radiusBound 31147 4139 718 (11/2) q ≤ 28/5 := by
  have hb : (1:ℝ) ≤ q.den := by exact_mod_cast q.pos
  have hd := div_le_div_of_nonneg_left (by positivity : 0 ≤ 10*Real.pi*718)
    (by norm_num : (0:ℝ) < 4139) (show (4139:ℝ) ≤ (q.den:ℝ)*4139 by nlinarith)
  unfold radiusBound
  norm_num at hd ⊢
  linarith [Real.pi_lt_d2]

theorem kappa_bound (q : ℚ) : kappa (radiusBound 31147 4139 718 (11/2) q) ≤ 3 := by
  have hm := ResonantErrorBudget.kappa_mono
    (a := radiusBound 31147 4139 718 (11/2) q) (b := 28/5)
    (by unfold radiusBound; positivity) (radius_bound q) (by linarith [Real.pi_gt_three])
  apply hm.trans
  unfold kappa
  have hp : (0:ℝ) < 4*Real.pi^2 := by positivity
  have hf : (28/5:ℝ)^2/(4*Real.pi^2) ≤ 4/5 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith [Real.pi_gt_d2]
  have hd : (12/5:ℝ) ≤ 12*(1-(28/5:ℝ)^2/(4*Real.pi^2)) := by linarith
  have hv : (28/5:ℝ)/(12*(1-(28/5:ℝ)^2/(4*Real.pi^2))) ≤ 5/2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hd)).mpr
    linarith
  linarith

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den ≤ 300) :
    2*eta+10*SmoothedLogTail.tail 718 eta+
      (3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139))+4*kappa (radiusBound 31147 4139 718 (11/2) q))*
        Real.log (2/eta)/(n:ℝ) ≤ (119/1000:ℝ)-1/4000 := by
  have hb' : (q.den:ℝ) ≤ 300 := by exact_mod_cast hb
  have hc : 3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139)) ≤ 220 := by norm_num; linarith
  have hk := kappa_bound q
  have hl := DenominatorOnePositiveCertificate.log_bound
  have hl0 : 0 ≤ Real.log (2/eta) := Real.log_nonneg (by norm_num [eta])
  have hm : (3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139))+4*kappa (radiusBound 31147 4139 718 (11/2) q))*
      Real.log (2/eta) ≤ 1392 := by
    have hmul := mul_le_mul_of_nonneg_right (show
      3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139))+4*kappa (radiusBound 31147 4139 718 (11/2) q) ≤ 232 by linarith) hl0
    nlinarith
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hd := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)
  have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1392) (by norm_num : (0:ℝ) < 31147) hn'
  have ht := DenominatorOnePositiveCertificate.tail_bound
  norm_num [eta] at *
  linarith

theorem polynomial_decay (n B : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hB : 2 ≤ B) (hb : q.den = 5*B) (hbmax : q.den ≤ 300)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  have hp := ResonantLimitPolynomial.five_norm_upper n 31147 4139 718 B τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) hτ hT (by norm_num [eta]) (by norm_num [eta]) hq
    ((radius_bound q).trans_lt (by linarith [Real.pi_gt_three])) (by omega) hb
  have hg := DivisibleResonantGap.scaled_gap B eta τ (DirichletCover.localAngle n θ q)
    hB (by norm_num [eta]) hτ hT
  have hs := DivisibleNonresonantBound.nonresonant_bound n 4139 718 B τ θ eta q
    (by norm_num) (by norm_num) hτ (by norm_num [eta]) (by norm_num [eta]) hq hb
  have hbgt := budget n q hn hbmax
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139))+4*kappa (radiusBound 31147 4139 718 (11/2) q))*
      Real.log (2/eta)/(n:ℝ) ≤ (119/1000:ℝ)-1/4000-2*eta-10*SmoothedLogTail.tail 718 eta by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem all_small_five (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hb : 5 ∣ q.den) (hbmax : q.den ≤ 300)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q)
    (hθ : OuterArcGeometry.region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  obtain ⟨B,hB⟩ := hb
  have hpos := q.pos
  by_cases hlarge : 2 ≤ B
  · exact polynomial_decay n B τ θ q hn hlarge hB hbmax hτ hT hq
  · have hb5 : q.den = 5 := by omega
    exact DenominatorFiveCertificate.polynomial_decay n τ θ q hn hτ hT hq hb5 hθ

end
end Borwein.SmallDivisibleCertificate
