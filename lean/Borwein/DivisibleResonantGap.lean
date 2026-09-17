import Borwein.SmallRadialBaseline
import Borwein.SmoothedPhase

set_option autoImplicit false

namespace Borwein.DivisibleResonantGap
noncomputable section
open PhaseIntegral PhaseGap DilogarithmUpper

theorem exp_endpoint : Real.exp (-(11/2:ℝ)) ≤ 1/202 := by
  have h1 : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h5 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 8/3) h1 5
  rw [← Real.exp_nat_mul] at h5
  norm_num at h5
  have hh : (3/2:ℝ) ≤ Real.exp (1/2) := by linarith [Real.add_one_le_exp (1/2:ℝ)]
  have hm := mul_le_mul h5 hh (by norm_num : (0:ℝ) ≤ 3/2) (Real.exp_pos 5).le
  rw [← Real.exp_add] at hm
  norm_num at hm
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem radial_endpoint : radial (11/2) ≤ 1/201 := by
  apply (DilogarithmTail.radial_upper (11/2) (1/202) (by norm_num) exp_endpoint (by norm_num)).trans
  apply (DilogarithmTail.series_upper 0 (1/202) (by norm_num) (by norm_num)).trans
  norm_num [Finset.sum_range_succ]

theorem radial_lower (τ : ℝ) (hτ : τ ≤ 11/2) : (119/500:ℝ) ≤ radialR τ := by
  apply le_trans _ (SmallRadialBaseline.radialR_antitone hτ)
  have h := PositiveRadialCusp.radial_lower (11/2) (by norm_num)
  have hC := PositiveCuspCertificate.constants_lower.2
  have hB := radial_endpoint
  norm_num at h
  linarith

theorem modulus_upper (η τ t : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) :
    SmoothedPhase.smoothedModulus η τ t ≤ radialR τ := by
  have h := SmoothedPhase.smoothedModulus_upper η τ t hη hτ
  have hi : 0 ≤ ∫ x in (0:ℝ)..1,
      SmoothedPhase.smoothedGap η τ t x+SmoothedPhase.smoothedGap η τ t x^2 := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x _
    have hg : 0 ≤ SmoothedPhase.smoothedGap η τ t x := by
      simpa [SmoothedPhase.smoothedGap, pairGap_eq_groupedGap] using
        pairGap_nonneg (radialWeight (η+τ*x)) (fun j => (j:ℝ)*(t*x))
          (fun j => (radialWeight_pos (η+τ*x) j).le)
    positivity
  linarith

theorem scaled_gap (B : ℕ) (η τ t : ℝ) (hB : 2 ≤ B)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    (119/1000:ℝ) ≤ radialR τ-
      SmoothedPhase.smoothedModulus (B*η) (B*τ) (B*t)/(B:ℝ) := by
  have hB' : (2:ℝ) ≤ B := by exact_mod_cast hB
  have hr := radial_lower τ hT
  have hm := modulus_upper (B*η) (B*τ) (B*t) (by positivity) (by positivity)
  have hmono := SmallRadialBaseline.radialR_antitone (show τ ≤ (B:ℝ)*τ by nlinarith)
  have hd := div_le_div_of_nonneg_right (hm.trans hmono) (Nat.cast_nonneg B)
  have hd' := div_le_div_of_nonneg_left (by linarith : 0 ≤ radialR τ) (by norm_num : (0:ℝ) < 2) hB'
  linarith

end
end Borwein.DivisibleResonantGap
