import Borwein.ElementaryPhaseConstants

set_option autoImplicit false

namespace Borwein.AngleDeficit
noncomputable section
open PhaseAngleRange ExplicitPhaseProfile ElementaryPhaseConstants

theorem uAngle_derivative (v : ℝ) :
    HasDerivAt uAngle ((c1/(1+(v*c1)^2)+2*c2/(1+(v*c2)^2))/5) v := by
  have h := ((((hasDerivAt_id v).mul_const c1).arctan).add
    ((((hasDerivAt_id v).mul_const c2).arctan).const_mul 2)).div_const 5
  apply h.congr_deriv
  dsimp
  ring

theorem angle_deficits (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    (1-v)/5 ≤ Real.pi/10-uAngle v ∧
      3*(1-v)/25 ≤ Real.pi/10-vAngle v := by
  have hu := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun x _ => (uAngle_derivative x).continuousAt.continuousWithinAt)
    (fun x _ => (uAngle_derivative x).differentiableAt.differentiableWithinAt)
    (C := (1/5:ℝ)) (fun x hx => by
      rw [(uAngle_derivative x).deriv]
      exact (angle_slopes x (interior_subset hx)).1)
    v hv 1 (by norm_num) hv.2
  have hw := (convex_Icc (0:ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun x _ => (vAngle_derivative x).continuousAt.continuousWithinAt)
    (fun x _ => (vAngle_derivative x).differentiableAt.differentiableWithinAt)
    (C := (3/25:ℝ)) (fun x hx => by
      rw [(vAngle_derivative x).deriv]
      exact (angle_slopes x (interior_subset hx)).2)
    v hv 1 (by norm_num) hv.2
  rw [endpoint_angles.2.2.1] at hu
  rw [endpoint_angles.2.2.2] at hw
  constructor <;> linarith

theorem parameter_complement (τ : ℝ) :
    1-parameter τ = 2*Real.exp (-τ)/(1+Real.exp (-τ)) := by
  have hd : 1+Real.exp (-τ) ≠ 0 := ne_of_gt (by positivity)
  unfold parameter
  field_simp
  <;> ring

theorem actual_deficits (τ : ℝ) (hτ : 0 ≤ τ) :
    (2/5:ℝ)*(Real.exp (-τ)/(1+Real.exp (-τ))) ≤ Real.pi/10-(alpha τ+2*beta τ)/5 ∧
      (6/25:ℝ)*(Real.exp (-τ)/(1+Real.exp (-τ))) ≤ Real.pi/10-(2*alpha τ-beta τ)/5 := by
  have hv := parameter_range τ hτ
  have h := angle_deficits (parameter τ) ⟨hv.1,hv.2.le⟩
  rw [parameter_complement] at h
  change (2*Real.exp (-τ)/(1+Real.exp (-τ)))/5 ≤ Real.pi/10-(alpha τ+2*beta τ)/5 ∧
    3*(2*Real.exp (-τ)/(1+Real.exp (-τ)))/25 ≤ Real.pi/10-(2*alpha τ-beta τ)/5 at h
  simp only [mul_div_assoc] at h
  constructor <;> linarith [h.1,h.2]

end
end Borwein.AngleDeficit
