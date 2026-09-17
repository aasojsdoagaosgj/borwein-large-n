import Borwein.ExplicitPhaseProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

namespace Borwein.PhaseAngleRange
noncomputable section
open ExplicitPhaseProfile

def c1 : ℝ := Real.cos (Real.pi/5)/Real.sin (Real.pi/5)
def c2 : ℝ := Real.cos (2*Real.pi/5)/Real.sin (2*Real.pi/5)
def uAngle (v : ℝ) : ℝ := (Real.arctan (v*c1)+2*Real.arctan (v*c2))/5
def vAngle (v : ℝ) : ℝ := (2*Real.arctan (v*c1)-Real.arctan (v*c2))/5

theorem c1_bounds : (1:ℝ) ≤ c1 ∧ c1 ≤ 7/5 := by
  have hp := Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi (by positivity : (0:ℝ) < Real.pi/5) (by linarith)
  have hc := Real.cos_pos_of_mem_Ioo (x := Real.pi/5) ⟨by linarith,by linarith⟩
  have hsc : Real.sin (Real.pi/5) ≤ Real.cos (Real.pi/5) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : (0:ℝ) ≤ Real.pi/5)
      (by linarith : Real.pi/2-Real.pi/5 ≤ Real.pi)
      (by linarith : Real.pi/5 ≤ Real.pi/2-Real.pi/5)
    rwa [Real.cos_pi_div_two_sub] at h
  have hslow : (7/12:ℝ) ≤ Real.sin (Real.pi/5) := by
    have ht := Real.sin_ge_sub_cube (by positivity : (0:ℝ) ≤ Real.pi/5)
    have hx : Real.pi/5 ≤ (16/25:ℝ) := by linarith [Real.pi_lt_d2]
    have hx3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.pi/5) hx 3
    have hl := Real.pi_gt_d2
    nlinarith
  constructor
  · exact (le_div_iff₀ hs).mpr (by simpa using hsc)
  · apply (div_le_iff₀ hs).mpr
    have hsq : Real.cos (Real.pi/5)^2 ≤ ((7/5:ℝ)*Real.sin (Real.pi/5))^2 := by
      nlinarith [Real.sin_sq_add_cos_sq (Real.pi/5)]
    exact (sq_le_sq₀ hc.le (by positivity)).mp hsq

theorem c2_bounds : (0:ℝ) < c2 ∧ c2 ≤ 2/3 := by
  have hp := Real.pi_pos
  have hs := Real.sin_pos_of_pos_of_lt_pi (by positivity : (0:ℝ) < 2*Real.pi/5) (by linarith)
  have hc := Real.cos_pos_of_mem_Ioo (x := 2*Real.pi/5) ⟨by linarith,by linarith⟩
  have hc1 : Real.cos (2*Real.pi/5) ≤ (1/2:ℝ) := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi
      (by positivity : (0:ℝ) ≤ Real.pi/3)
      (by linarith : 2*Real.pi/5 ≤ Real.pi)
      (by linarith : Real.pi/3 ≤ 2*Real.pi/5)
    rwa [Real.cos_pi_div_three] at h
  have hs1 : (3/4:ℝ) ≤ Real.sin (2*Real.pi/5) := by
    nlinarith [Real.sin_sq_add_cos_sq (2*Real.pi/5)]
  constructor
  · exact div_pos hc hs
  · apply (div_le_iff₀ hs).mpr
    linarith

theorem arctan_cot (t : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi/2) :
    Real.arctan (Real.cos t/Real.sin t) = Real.pi/2-t := by
  have he : Real.tan (Real.pi/2-t) = Real.cos t/Real.sin t := by
    rw [Real.tan_pi_div_two_sub,Real.tan_eq_sin_div_cos,inv_div]
  rw [← he]
  exact Real.arctan_tan (by linarith) (by linarith)

theorem endpoint_angles : uAngle 0 = 0 ∧ vAngle 0 = 0 ∧
    uAngle 1 = Real.pi/10 ∧ vAngle 1 = Real.pi/10 := by
  have h1 := arctan_cot (Real.pi/5) (by positivity) (by linarith [Real.pi_pos])
  have h2 := arctan_cot (2*Real.pi/5) (by positivity) (by linarith [Real.pi_pos])
  norm_num only [uAngle,vAngle,zero_mul,one_mul,Real.arctan_zero,mul_zero,zero_add,
    sub_zero,zero_div,true_and]
  dsimp [c1,c2]
  rw [h1,h2]
  constructor <;> ring

theorem uAngle_strictMono : StrictMono uAngle := by
  intro x y hxy
  have h1 := Real.arctan_strictMono (mul_lt_mul_of_pos_right hxy (by linarith [c1_bounds.1] : 0 < c1))
  have h2 := Real.arctan_strictMono (mul_lt_mul_of_pos_right hxy c2_bounds.1)
  unfold uAngle
  linarith

theorem vAngle_derivative (v : ℝ) :
    HasDerivAt vAngle ((2*c1/(1+(v*c1)^2)-c2/(1+(v*c2)^2))/5) v := by
  have h := (((((hasDerivAt_id v).mul_const c1).arctan).const_mul 2).sub
    (((hasDerivAt_id v).mul_const c2).arctan)).div_const 5
  apply h.congr_deriv
  dsimp
  ring

theorem vAngle_slope_lower (v : ℝ) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    (1/555:ℝ) ≤ (2*c1/(1+(v*c1)^2)-c2/(1+(v*c2)^2))/5 := by
  have hc1 := c1_bounds
  have hc2 := c2_bounds
  have hvc0 : 0 ≤ v*c1 := mul_nonneg hv.1 (by linarith)
  have hvc : v*c1 ≤ (7/5:ℝ) :=
    (mul_le_mul_of_nonneg_right hv.2 (by linarith : 0 ≤ c1)).trans (by simpa using hc1.2)
  have hvc2 := pow_le_pow_left₀ hvc0 hvc 2
  have hd1 : 0 < 1+(v*c1)^2 := by positivity
  have hd2 : 0 < 1+(v*c2)^2 := by positivity
  have hfirst : (25/37:ℝ) ≤ 2*c1/(1+(v*c1)^2) := by
    apply (le_div_iff₀ hd1).mpr
    nlinarith [hc1.1]
  have hsecond : c2/(1+(v*c2)^2) ≤ (2/3:ℝ) := by
    apply (div_le_iff₀ hd2).mpr
    nlinarith [sq_nonneg (v*c2),hc2.2]
  linarith

theorem vAngle_strictMonoOn : StrictMonoOn vAngle (Set.Icc (0:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 1)
  · exact fun x _ => (vAngle_derivative x).continuousAt.continuousWithinAt
  · intro x hx
    rw [(vAngle_derivative x).deriv]
    have h := vAngle_slope_lower x (interior_subset hx)
    linarith

theorem angle_ranges (τ : ℝ) (hτ : 0 ≤ τ) :
    (0 ≤ (alpha τ+2*beta τ)/5 ∧ (alpha τ+2*beta τ)/5 < Real.pi/10) ∧
    (0 ≤ (2*alpha τ-beta τ)/5 ∧ (2*alpha τ-beta τ)/5 < Real.pi/10) := by
  have hv := parameter_range τ hτ
  have hmem : parameter τ ∈ Set.Icc (0:ℝ) 1 := ⟨hv.1,hv.2.le⟩
  have hu0 := uAngle_strictMono.monotone hv.1
  have hu1 := uAngle_strictMono hv.2
  have hv0 := vAngle_strictMonoOn.monotoneOn (by norm_num : (0:ℝ) ∈ Set.Icc 0 1) hmem hv.1
  have hv1 := vAngle_strictMonoOn hmem (by norm_num : (1:ℝ) ∈ Set.Icc 0 1) hv.2
  rw [endpoint_angles.1] at hu0
  rw [endpoint_angles.2.2.1] at hu1
  rw [endpoint_angles.2.1] at hv0
  rw [endpoint_angles.2.2.2] at hv1
  exact ⟨⟨hu0,hu1⟩,⟨hv0,hv1⟩⟩

end
end Borwein.PhaseAngleRange
