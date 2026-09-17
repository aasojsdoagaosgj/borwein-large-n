import Borwein.ResidueGeometricBound
import Borwein.WeightedDilogCertificate
import Borwein.SmallCoprimeCertificate

set_option autoImplicit false

namespace Borwein.LargeCoprimeCertificate
noncomputable section
open PositiveCuspCertificate ResonantArgumentBounds ExponentialKernelRemainder

def cost (q : ℚ) : ℝ := ResidueGeometricBound.frequencyCost q 718 4139 1 eta+
  ResidueGeometricBound.frequencyCost q 718 4139 5 eta

theorem cost_envelope (q : ℚ) : cost q ≤
    (q.den:ℝ)*(39/25)/2+(q.den:ℝ)*(GeneralDenominatorVariation.multiplicity q 718:ℝ)*
      (1+1/3421+5/549)*(33/20)/2 := by
  have hD := mul_le_mul_of_nonneg_left WeightedDilogCertificate.radial_double (Nat.cast_nonneg q.den)
  have hpi : Real.pi^2/6 ≤ (33/20:ℝ) := by nlinarith [Real.pi_lt_d4,Real.pi_pos]
  have hA := mul_le_mul_of_nonneg_left hpi
    (mul_nonneg (Nat.cast_nonneg q.den) (Nat.cast_nonneg (GeneralDenominatorVariation.multiplicity q 718)))
  unfold cost ResidueGeometricBound.frequencyCost
  norm_num at *
  nlinarith

theorem middle_cost (q : ℚ) (hb : q.den ≤ 1436) : cost q ≤ 5000 := by
  have hm : q.den*GeneralDenominatorVariation.multiplicity q 718 ≤ 4308 := by
    have hc : ¬ 2*718 < q.den := by omega
    simp only [GeneralDenominatorVariation.multiplicity,hc,if_false,ResidueBlockCount.blocks]
    have hd := Nat.div_mul_le_self (718+q.den-1) q.den
    have hp := q.pos
    have hu : 718+q.den-1 ≤ 718+q.den := Nat.sub_le _ _
    nlinarith
  have hm' : (q.den:ℝ)*(GeneralDenominatorVariation.multiplicity q 718:ℝ) ≤ 4308 := by exact_mod_cast hm
  have hb' : (q.den:ℝ) ≤ 1436 := by exact_mod_cast hb
  have h := cost_envelope q
  nlinarith

theorem large_cost (q : ℚ) (hb : 1436 < q.den) (hQ : q.den ≤ 4139) : cost q ≤ 6680 := by
  have hm : GeneralDenominatorVariation.multiplicity q 718 = 1 := by
    simp [GeneralDenominatorVariation.multiplicity,show 2*718 < q.den by omega]
  have h := cost_envelope q
  rw [hm] at h
  have hb' : (q.den:ℝ) ≤ 4139 := by exact_mod_cast hQ
  norm_num at h
  linarith

theorem radius_bound (q : ℚ) (hb : 101 ≤ q.den) : radiusBound 31147 4139 718 (11/2) q ≤ 1 := by
  have hb' : (101:ℝ) ≤ q.den := by exact_mod_cast hb
  have hd := div_le_div_of_nonneg_left (by positivity : 0 ≤ 10*Real.pi*718)
    (by norm_num : (0:ℝ) < 101*4139) (show (101:ℝ)*4139 ≤ (q.den:ℝ)*4139 by nlinarith)
  unfold radiusBound
  norm_num at hd ⊢
  linarith [Real.pi_lt_d2]

theorem kappa_bound (q : ℚ) (hb : 101 ≤ q.den) : kappa (radiusBound 31147 4139 718 (11/2) q) ≤ 1 := by
  have hm := ResonantErrorBudget.kappa_mono
    (a := radiusBound 31147 4139 718 (11/2) q) (b := 1)
    (by unfold radiusBound; positivity) (radius_bound q hb) (by linarith [Real.pi_gt_three])
  apply hm.trans
  unfold kappa
  have hpi : 1/(4*Real.pi^2) ≤ (1/4:ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi^2)).mpr
    nlinarith [Real.pi_gt_three]
  norm_num only [one_pow] at *
  have hd : (9:ℝ) ≤ 12*(1-1/(4*Real.pi^2)) := by linarith
  have hv : 1/(12*(1-1/(4*Real.pi^2))) ≤ (1/2:ℝ) :=
    (div_le_iff₀ (by linarith)).mpr (by linarith)
  linarith

theorem budget (n : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hb : 101 ≤ q.den) (hQ : q.den ≤ 4139) :
    2*eta+10*SmoothedLogTail.tail 718 eta+2/(q.den:ℝ)+
      (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ)
        ≤ (119/500:ℝ)-1/4000 := by
  have hk := kappa_bound q hb
  have hl := DenominatorOnePositiveCertificate.log_bound
  have hl0 : 0 ≤ Real.log (2/eta) := Real.log_nonneg (by norm_num [eta])
  have he : 4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 24 := by
    have hm := mul_le_mul_of_nonneg_right hk hl0
    nlinarith
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have ht := DenominatorOnePositiveCertificate.tail_bound
  by_cases hm : q.den ≤ 1436
  · have hc := middle_cost q hm
    have hd := div_le_div_of_nonneg_right (show cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 5024 by linarith) (Nat.cast_nonneg n)
    have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 5024) (by norm_num : (0:ℝ) < 31147) hn'
    have hp := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 101) (show (101:ℝ) ≤ q.den by exact_mod_cast hb)
    norm_num [eta] at *
    linarith
  · have hc := large_cost q (by omega) hQ
    have hd := div_le_div_of_nonneg_right (show cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta) ≤ 6704 by linarith) (Nat.cast_nonneg n)
    have hd' := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 6704) (by norm_num : (0:ℝ) < 31147) hn'
    have hp := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (0:ℝ) < 1437) (show (1437:ℝ) ≤ q.den by exact_mod_cast (show 1437 ≤ q.den by omega))
    norm_num [eta] at *
    linarith

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hb : 101 ≤ q.den) (hc : q.den.Coprime 5)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
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
  have hbgt := budget n q hn hb hq.1
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ) ≤
      (119/500:ℝ)-1/4000-2*eta-10*SmoothedLogTail.tail 718 eta-2/(q.den:ℝ) by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem all_coprime (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hc : q.den.Coprime 5)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  by_cases hb1 : q.den = 1
  · exact CertifiedDenominatorOne.polynomial_decay n τ θ q hn hτ hT hq hb1
  by_cases hsmall : q.den ≤ 100
  · exact SmallCoprimeCertificate.polynomial_decay n τ θ q hn (by have hp := q.pos; omega) hsmall hc hτ hT hq
  · exact polynomial_decay n τ θ q hn (by omega) hc hτ hT hq

end
end Borwein.LargeCoprimeCertificate
