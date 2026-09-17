import Borwein.LargeDivisibleNonresonant
import Borwein.LargeCoprimeCertificate

set_option autoImplicit false

namespace Borwein.LargeDivisibleCertificate
noncomputable section
open PositiveCuspCertificate ResonantArgumentBounds ExponentialKernelRemainder

def cost (q : ℚ) : ℝ := ResidueGeometricBound.frequencyCost q 718 4139 1 eta+
  ResidueGeometricBound.frequencyCost ((5:ℚ)*q) 718 4139 1 eta

theorem frequency_envelope (q : ℚ) : ResidueGeometricBound.frequencyCost q 718 4139 1 eta ≤
    (q.den:ℝ)*(39/25)/4+(q.den:ℝ)*(GeneralDenominatorVariation.multiplicity q 718:ℝ)*
      (1/2+1/3421)*(33/20)/2 := by
  have hD := mul_le_mul_of_nonneg_left WeightedDilogCertificate.radial_double (Nat.cast_nonneg q.den)
  have hpi : Real.pi^2/6 ≤ (33/20:ℝ) := by nlinarith [Real.pi_lt_d4,Real.pi_pos]
  have hA := mul_le_mul_of_nonneg_left hpi
    (mul_nonneg (Nat.cast_nonneg q.den) (Nat.cast_nonneg (GeneralDenominatorVariation.multiplicity q 718)))
  unfold ResidueGeometricBound.frequencyCost
  norm_num at *
  nlinarith

theorem multiplicity_product (q : ℚ) (hb : q.den ≤ 1436) :
    q.den*GeneralDenominatorVariation.multiplicity q 718 ≤ 2*(718+q.den) := by
  have hc : ¬ 2*718 < q.den := by omega
  simp only [GeneralDenominatorVariation.multiplicity,hc,if_false,ResidueBlockCount.blocks]
  have hd := Nat.div_mul_le_self (718+q.den-1) q.den
  have hu : 718+q.den-1 ≤ 718+q.den := Nat.sub_le _ _
  nlinarith

theorem first_cost (q : ℚ) (hQ : q.den ≤ 4139) : ResidueGeometricBound.frequencyCost q 718 4139 1 eta ≤ 3400 := by
  have h := frequency_envelope q
  by_cases hb : q.den ≤ 1436
  · have hm := multiplicity_product q hb
    have hm' : (q.den:ℝ)*(GeneralDenominatorVariation.multiplicity q 718:ℝ) ≤ 4308 := by
      exact_mod_cast (show q.den*GeneralDenominatorVariation.multiplicity q 718 ≤ 4308 by omega)
    have hb' : (q.den:ℝ) ≤ 1436 := by exact_mod_cast hb
    nlinarith
  · have hm : GeneralDenominatorVariation.multiplicity q 718 = 1 := by
      simp [GeneralDenominatorVariation.multiplicity,show 2*718 < q.den by omega]
    rw [hm] at h
    have hb' : (q.den:ℝ) ≤ 4139 := by exact_mod_cast hQ
    norm_num at h
    linarith

theorem reduced_cost (q : ℚ) (hb : q.den ≤ 827) : ResidueGeometricBound.frequencyCost q 718 4139 1 eta ≤ 1600 := by
  have h := frequency_envelope q
  have hm := multiplicity_product q (by omega)
  have hm' : (q.den:ℝ)*(GeneralDenominatorVariation.multiplicity q 718:ℝ) ≤ 3090 := by
    exact_mod_cast (show q.den*GeneralDenominatorVariation.multiplicity q 718 ≤ 3090 by omega)
  have hb' : (q.den:ℝ) ≤ 827 := by exact_mod_cast hb
  nlinarith

theorem cost_bound (q : ℚ) (B : ℕ) (hb : q.den = 5*B) (hQ : q.den ≤ 4139) : cost q ≤ 5000 := by
  have h1 := first_cost q hQ
  have h5 := reduced_cost ((5:ℚ)*q) (by rw [ReducedFiveFrequency.scaled_den q B hb]; omega)
  unfold cost
  linarith

theorem radial_zero : PhaseIntegral.radialR 0 = Real.log 5 := by
  simp [PhaseIntegral.radialR,PhaseIntegral.radialSum]

theorem modulus_upper (η τ t : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) :
    SmoothedPhase.smoothedModulus η τ t ≤ 2 := by
  have hm := DivisibleResonantGap.modulus_upper η τ t hη hτ
  have hr := SmallRadialBaseline.radialR_antitone hτ
  rw [radial_zero] at hr
  have hl : Real.log 5 ≤ (2:ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 5)).mpr
    have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) he 2
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp
    linarith
  linarith

theorem budget (n B : ℕ) (q : ℚ) (hn : 31147 ≤ n) (hB : 61 ≤ B)
    (hb : q.den = 5*B) (hQ : q.den ≤ 4139) :
    2*eta+10*SmoothedLogTail.tail 718 eta+2/(B:ℝ)+
      (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ)
        ≤ (119/500:ℝ)-1/4000 := by
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

theorem polynomial_decay (n B : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hB : 61 ≤ B) (hb : q.den = 5*B)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
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
  have hbgt := budget n B q hn hB hb hq.1
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    (cost q+4*kappa (radiusBound 31147 4139 718 (11/2) q)*Real.log (2/eta))/(n:ℝ) ≤
      (119/500:ℝ)-1/4000-2*eta-10*SmoothedLogTail.tail 718 eta-2/(B:ℝ) by linarith)
  apply hp.trans
  apply Real.exp_le_exp.mpr
  nlinarith

theorem all_divisible (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hb : 5 ∣ q.den) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hθ : OuterArcGeometry.region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  by_cases hsmall : q.den ≤ 300
  · exact SmallDivisibleCertificate.all_small_five n τ θ q hn hb hsmall hτ hT hq hθ
  obtain ⟨B,hB⟩ := hb
  exact polynomial_decay n B τ θ q hn (by omega) hB hτ hT hq

end
end Borwein.LargeDivisibleCertificate
