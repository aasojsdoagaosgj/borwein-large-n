import Borwein.EntropyUpper
import Borwein.DilogarithmTail

set_option autoImplicit false

namespace Borwein.PositiveCuspCertificate
noncomputable section
open Complex PositiveRadialCusp DilogarithmUpper DilogarithmTail EntropyUpper
  RadialSmoothingIncrement SmoothedResonantMain

def eta : ℝ := 11313/1250000

theorem constants_lower : (41/25:ℝ) ≤ A ∧ (657/500:ℝ) ≤ C := by
  unfold A C
  constructor <;> nlinarith [Real.pi_gt_d2]

theorem numerator_half : (91/375:ℝ) ≤ numerator (1/2) := by
  have hA := constants_lower.1
  have hC := constants_lower.2
  have hB := radial_half
  have h0 := radial_nonneg (1/2)
  have hsq : (radial (1/2))^2/A ≤ 1/3 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hA)).mpr
    nlinarith
  unfold numerator
  linarith

theorem numerator_one : (397/500:ℝ) ≤ numerator 1 := by
  have hA := constants_lower.1
  have hC := constants_lower.2
  have hB := radial_one
  have h0 := radial_nonneg 1
  have hsq : (radial 1)^2/A ≤ 11/100 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hA)).mpr
    nlinarith
  unfold numerator
  linarith

theorem entropy_first (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1) : entropy (eta/τ) ≤ 6*eta/τ := by
  have h := ratio_upper eta τ 5 (by norm_num [eta]) hτ (by
    have he := exp_five_lower
    norm_num [eta]
    linarith)
  exact h.trans_eq (by ring)

theorem entropy_second (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 11/2) : entropy (eta/τ) ≤ 8*eta/τ := by
  have h := ratio_upper eta τ 7 (by norm_num [eta]) hτ (by
    have he := exp_seven_lower
    norm_num [eta]
    linarith)
  exact h.trans_eq (by ring)

theorem first_band (τ t : ℝ) (hτ0 : 1/2 ≤ τ) (hτ1 : τ ≤ 1) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 eta ((τ:ℂ)-(t:ℂ)*I) := by
  have hτ : 0 < τ := by linarith
  have hN := (numerator_half).trans (numerator_mono (by norm_num) hτ0)
  have hH := entropy_first τ hτ hτ1
  have hG := denominator_one_gap eta τ t (by norm_num [eta]) hτ
  have he : (91/375:ℝ)-24*eta ≥ 1/40 := by norm_num [eta]
  have hmul : (1/40:ℝ)*τ ≤ numerator τ-24*eta := by nlinarith
  have hd := (le_div_iff₀ hτ).mpr hmul
  have hr : (numerator τ-24*eta)/τ = numerator τ/τ-4*(6*eta/τ) := by ring
  rw [hr] at hd
  linarith

theorem second_band (τ t : ℝ) (hτ0 : 1 ≤ τ) (hτ1 : τ ≤ 11/2) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 eta ((τ:ℂ)-(t:ℂ)*I) := by
  have hτ : 0 < τ := by linarith
  have hN := numerator_one.trans (numerator_mono (by norm_num) hτ0)
  have hH := entropy_second τ hτ hτ1
  have hG := denominator_one_gap eta τ t (by norm_num [eta]) hτ
  have he : (397/500:ℝ)-32*eta ≥ (1/40)*(11/2) := by norm_num [eta]
  have hmul : (1/40:ℝ)*τ ≤ numerator τ-32*eta := by nlinarith
  have hd := (le_div_iff₀ hτ).mpr hmul
  have hr : (numerator τ-32*eta)/τ = numerator τ/τ-4*(8*eta/τ) := by ring
  rw [hr] at hd
  linarith

theorem positive_gap (τ t : ℝ) (hτ0 : 1/2 ≤ τ) (hτ1 : τ ≤ 11/2) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 eta ((τ:ℂ)-(t:ℂ)*I) := by
  by_cases hτ : τ ≤ 1
  · exact first_band τ t hτ0 hτ
  · exact second_band τ t (by linarith) hτ1

end
end Borwein.PositiveCuspCertificate
