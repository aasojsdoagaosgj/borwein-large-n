import Borwein.CertifiedOuterLocalization

set_option autoImplicit false

namespace Borwein.SharpDenominatorFive
noncomputable section
open ResonantArgumentBounds ExponentialKernelRemainder

theorem tail_numerator : (Real.exp (-(113/40000:ℝ)))^(2717+1) ≤ 473/1000000 := by
  have he : Real.exp (-(113/40000:ℝ)*2718/8) ≤ 48/125 := by
    apply (ExpCertificate.exp_enclosure _ 0 (48/125) 12 (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 8
  have hid : (Real.exp (-(113/40000:ℝ)))^(2717+1) =
      (Real.exp (-(113/40000:ℝ)*2718/8))^8 := by
    rw [← Real.exp_nat_mul,← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hid]
  exact hp.trans (by norm_num)

theorem tail_bound : SmoothedLogTail.tail 2717 (113/40000) ≤ 1/16000 := by
  have he := ExpCertificate.exp_eta_bounds.2
  have hd : (7/2500:ℝ) ≤ 1-Real.exp (-(113/40000:ℝ)) := by
    norm_num [ExpCertificate.etaHi,ExpCertificate.scale] at he
    linarith
  unfold SmoothedLogTail.tail
  rw [← div_eq_mul_inv]
  apply (div_le_div₀ (by positivity) (div_le_div_of_nonneg_right tail_numerator (by positivity))
    (by norm_num : (0:ℝ) < 7/2500) hd).trans
  norm_num

theorem log_bound : Real.log (2/(113/40000:ℝ)) ≤ 33/5 := by
  have he : (271/100:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 271/100) he 6
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hs : (9/5:ℝ) ≤ Real.exp (3/5) := by
    apply (ExpCertificate.exp_enclosure _ (9/5) 2 12 (by norm_num) (by norm_num) ?_ ?_).1
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  have hm := mul_le_mul hp hs (by norm_num : (0:ℝ) ≤ 9/5) (Real.exp_pos 6).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  apply (Real.log_le_iff_le_exp (by norm_num)).mpr
  linarith

theorem kappa_bound (q : ℚ) (hb : q.den = 5) :
    kappa (radiusBound 31147 4139 2717 (11/2) q) ≤ 7/5 := by
  have hm := ResonantErrorBudget.kappa_mono
    (a := radiusBound 31147 4139 2717 (11/2) q) (b := 47/10)
    (by unfold radiusBound; positivity) (DenominatorFiveCertificate.radius_bound q hb) (by linarith [Real.pi_gt_three])
  apply hm.trans
  unfold kappa
  have hf : (47/10:ℝ)^2/(4*Real.pi^2) ≤ 9/16 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi^2)).mpr
    nlinarith [Real.pi_gt_d2]
  have hd : (21/4:ℝ) ≤ 12*(1-(47/10:ℝ)^2/(4*Real.pi^2)) := by linarith
  have hv : (47/10:ℝ)/(12*(1-(47/10:ℝ)^2/(4*Real.pi^2))) ≤ 9/10 :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den = 5) :
    2*(113/40000:ℝ)+10*SmoothedLogTail.tail 2717 (113/40000)+
      (5/(2*(1-(2717:ℝ)/4139))+4*kappa (radiusBound 31147 4139 2717 (11/2) q))*
        Real.log (2/(113/40000))/(n:ℝ) ≤ (31:ℝ)/3125-9/10000 := by
  have hc : 5/(2*(1-(2717:ℝ)/4139))+4*kappa (radiusBound 31147 4139 2717 (11/2) q) ≤ 129/10 := by
    have hk := kappa_bound q hb
    norm_num
    linarith
  have hl0 : 0 ≤ Real.log (2/(113/40000:ℝ)) := Real.log_nonneg (by norm_num)
  have hm : (5/(2*(1-(2717:ℝ)/4139))+4*kappa (radiusBound 31147 4139 2717 (11/2) q))*
      Real.log (2/(113/40000)) ≤ 426/5 := by
    have h1 := mul_le_mul_of_nonneg_right hc hl0
    have h2 := mul_le_mul_of_nonneg_left log_bound (by norm_num : (0:ℝ) ≤ 129/10)
    linarith
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hd := div_le_div_of_nonneg_right hm (Nat.cast_nonneg n)
  have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 426/5) (by norm_num : (0:ℝ) < 31147) hn'
  linarith [tail_bound]

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 5)
    (hθ : OuterArcGeometry.region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-9/10000)) := by
  exact NonresonantGeometricBound.denominator_five_decay n 31147 4139 2717 τ θ (9/10000) q
    (by norm_num) hn (by norm_num) (by norm_num) hτ hT hq
    ((DenominatorFiveCertificate.radius_bound q hb).trans_lt (by linarith [Real.pi_gt_three])) hb hθ (budget n q hn hb)

end
end Borwein.SharpDenominatorFive
