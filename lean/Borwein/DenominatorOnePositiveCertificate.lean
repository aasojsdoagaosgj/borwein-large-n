import Borwein.PositiveCuspCertificate

set_option autoImplicit false

namespace Borwein.DenominatorOnePositiveCertificate
noncomputable section
open PositiveCuspCertificate ResonantArgumentBounds ExponentialKernelRemainder

theorem tail_numerator : (Real.exp (-eta))^(718+1) ≤ 1/650 := by
  have he : Real.exp (-eta*719/7) ≤ 79/200 := by
    apply (ExpCertificate.exp_enclosure _ 0 (79/200) 12 (by norm_num [eta]) (by norm_num) ?_ ?_).2
    all_goals norm_num [eta,ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 7
  have hid : (Real.exp (-eta))^(718+1) = (Real.exp (-eta*719/7))^7 := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
    congr 1
    ring
  rw [hid]
  exact hp.trans (by norm_num)

theorem tail_bound : SmoothedLogTail.tail 718 eta ≤ 1/4000 := by
  have he : Real.exp (-eta) ≤ 991/1000 := by
    apply (ExpCertificate.exp_enclosure _ 0 (991/1000) 12 (by norm_num [eta]) (by norm_num) ?_ ?_).2
    all_goals norm_num [eta,ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  have hd : (9/1000:ℝ) ≤ 1-Real.exp (-eta) := by linarith
  unfold SmoothedLogTail.tail
  rw [← div_eq_mul_inv]
  apply (div_le_div₀ (by positivity) (div_le_div_of_nonneg_right tail_numerator (by positivity))
    (by norm_num : (0:ℝ) < 9/1000) hd).trans
  norm_num

theorem log_bound : Real.log (2/eta) ≤ 6 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he 6
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  apply (Real.log_le_iff_le_exp (by norm_num [eta])).mpr
  norm_num [eta]
  linarith

theorem radius_bound (q : ℚ) (hb : q.den = 1) :
    radiusBound 31147 4139 718 (11/2) q ≤ 28/5 := by
  unfold radiusBound
  rw [hb]
  norm_num
  linarith [Real.pi_lt_d2]

theorem kappa_bound (q : ℚ) (hb : q.den = 1) :
    kappa (radiusBound 31147 4139 718 (11/2) q) ≤ 3 := by
  have hm := ResonantErrorBudget.kappa_mono
    (a := radiusBound 31147 4139 718 (11/2) q) (b := 28/5)
    (by unfold radiusBound; positivity) (radius_bound q hb) (by linarith [Real.pi_gt_three])
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

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den = 1) :
    2*eta+10*SmoothedLogTail.tail 718 eta+
      4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta)/(n:ℝ)
          ≤ (1/40:ℝ)-1/4000 := by
  have hk := kappa_bound q hb
  have hl0 : 0 ≤ Real.log (2/eta) := Real.log_nonneg (by norm_num [eta])
  have hm : 4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 72 := by
    have h1 := mul_le_mul_of_nonneg_right hk hl0
    have h2 := log_bound
    nlinarith
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hd := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)
  have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 72) (by norm_num : (0:ℝ) < 31147) hn'
  have ht := tail_bound
  norm_num [eta] at *
  linarith

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 1/2 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  have hp := ResonantLimitPolynomial.denominator_one n 31147 4139 718 τ (11/2) θ eta q
    (by norm_num) hn (by norm_num) (by linarith) hτ1 (by norm_num [eta]) (by norm_num [eta]) hq
    ((radius_bound q hb).trans_lt (by linarith [Real.pi_gt_three])) hb
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hg := positive_gap τ (DirichletCover.localAngle n θ q) hτ0 hτ1
  have hbgt := budget n q hn hb
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta)/(n:ℝ) ≤
      (1/40:ℝ)-1/4000-2*eta-10*SmoothedLogTail.tail 718 eta by linarith)
  nlinarith

end
end Borwein.DenominatorOnePositiveCertificate
