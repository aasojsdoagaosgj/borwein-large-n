import Borwein.CertifiedOuterLocalization

set_option autoImplicit false

namespace Borwein.SharpSharedBudgets
noncomputable section
open PositiveCuspCertificate ResonantArgumentBounds ExponentialKernelRemainder

namespace One
open DenominatorOnePositiveCertificate

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den = 1) :
    2*eta+10*SmoothedLogTail.tail 718 eta+
      4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta)/(n:ℝ)
          ≤ (1/40:ℝ)-9/10000 := by
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
end One

namespace SmallCoprime
open SmallCoprimeCertificate

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den ≤ 100) :
    2*eta+10*SmoothedLogTail.tail 718 eta+
      (coefficient q+4*kappa (radiusBound 31147 4139 718 (11/2) q))*Real.log (2/eta)/(n:ℝ)
        ≤ (13/100:ℝ)-9/10000 := by
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
end SmallCoprime

namespace SmallDivisible
open SmallDivisibleCertificate

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : q.den ≤ 300) :
    2*eta+10*SmoothedLogTail.tail 718 eta+
      (3*(q.den:ℝ)/(5*(1-(718:ℝ)/4139))+4*kappa (radiusBound 31147 4139 718 (11/2) q))*
        Real.log (2/eta)/(n:ℝ) ≤ (119/1000:ℝ)-9/10000 := by
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
end SmallDivisible

namespace LargeCoprime
open LargeCoprimeCertificate

theorem kappa_bound (q : ℚ) (hb : 101 ≤ q.den) :
    kappa (radiusBound 31147 4139 718 (11/2) q) ≤ 3/5 := by
  have hm := ResonantErrorBudget.kappa_mono
    (a := radiusBound 31147 4139 718 (11/2) q) (b := 1)
    (by unfold radiusBound; positivity) (LargeCoprimeCertificate.radius_bound q hb)
    (by linarith [Real.pi_gt_three])
  apply hm.trans
  unfold kappa
  have hf : 1/(4*Real.pi^2) ≤ (1/10:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi^2)).mpr
    nlinarith [Real.pi_gt_three]
  norm_num only [one_pow]
  have hd : (54/5:ℝ) ≤ 12*(1-1/(4*Real.pi^2)) := by linarith
  have hv : 1/(12*(1-1/(4*Real.pi^2))) ≤ (1/10:ℝ) :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : 101 ≤ q.den) (hQ : q.den ≤ 4139) :
    2*eta+10*SmoothedLogTail.tail 718 eta+2/(q.den:ℝ)+
      (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ)
        ≤ (119/500:ℝ)-9/10000 := by
  have hk := kappa_bound q hb
  have hl := DenominatorOnePositiveCertificate.log_bound
  have hl0 : 0 ≤ Real.log (2/eta) := Real.log_nonneg (by norm_num [eta])
  have he : 4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 72/5 := by
    have hm := mul_le_mul_of_nonneg_right hk hl0
    nlinarith
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have ht := DenominatorOnePositiveCertificate.tail_bound
  by_cases hm : q.den ≤ 1436
  · have hc := middle_cost q hm
    have hd := div_le_div_of_nonneg_right (show cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ (25072/5) by linarith) (Nat.cast_nonneg n)
    have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ (25072/5)) (by norm_num : (0:ℝ) < 31147) hn'
    have hp := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 101) (show (101:ℝ) ≤ q.den by exact_mod_cast hb)
    norm_num [eta] at *
    linarith
  · have hc := large_cost q (by omega) hQ
    have hd := div_le_div_of_nonneg_right (show cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ (33472/5) by linarith) (Nat.cast_nonneg n)
    have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ (33472/5)) (by norm_num : (0:ℝ) < 31147) hn'
    have hp := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 1437) (show (1437:ℝ) ≤ q.den by exact_mod_cast (show 1437 ≤ q.den by omega))
    norm_num [eta] at *
    linarith
end LargeCoprime

namespace LargeDivisible
open LargeDivisibleCertificate

theorem budget (n B : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hB : 61 ≤ B)
    (hb : q.den = 5*B) (hQ : q.den ≤ 4139) :
    2*eta+10*SmoothedLogTail.tail 718 eta+2/(B:ℝ)+
      (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ)
        ≤ (119/500:ℝ)-9/10000 := by
  have hk := LargeCoprimeCertificate.kappa_bound q (by omega)
  have hl := DenominatorOnePositiveCertificate.log_bound
  have hl0 : 0 ≤ Real.log (2/eta) := Real.log_nonneg (by norm_num [eta])
  have he : 4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 24 := by
    have hm := mul_le_mul_of_nonneg_right hk hl0
    nlinarith
  have hc := cost_bound q B hb hQ
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have ht := DenominatorOnePositiveCertificate.tail_bound
  have hd := div_le_div_of_nonneg_right (show cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 5024 by linarith) (Nat.cast_nonneg n)
  have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 5024) (by norm_num : (0:ℝ) < 31147) hn'
  have hp := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 61) (show (61:ℝ) ≤ B by exact_mod_cast hB)
  norm_num [eta] at *
  linarith
end LargeDivisible

end
end Borwein.SharpSharedBudgets
