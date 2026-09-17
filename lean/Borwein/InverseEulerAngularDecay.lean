import Borwein.InverseEulerNearLoss

set_option autoImplicit false

namespace Borwein.InverseEulerAngularDecay
noncomputable section
open Complex InverseEulerLoss InverseEulerNearLoss PeriodicRadialProfile

def offset (t : ℝ) : ℝ := t-2*Real.pi*(round (t/(2*Real.pi)):ℝ)

theorem offset_bound (t : ℝ) : |offset t| ≤ Real.pi := by
  have h := mul_le_mul_of_nonneg_left (abs_sub_round (t/(2*Real.pi)))
    (by positivity : (0:ℝ) ≤ 2*Real.pi)
  have he : offset t = (2*Real.pi)*(t/(2*Real.pi)-(round (t/(2*Real.pi)):ℝ)) := by
    unfold offset
    field_simp
  rw [he, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
  exact h.trans_eq (by ring)

theorem ray_offset (u t : ℝ) : ray u (offset t) = ray u t := by
  have he : exp (((2*Real.pi*(round (t/(2*Real.pi)):ℝ):ℂ))*I) = 1 := by
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨round (t/(2*Real.pi)), ?_⟩
    push_cast
    ring
  have hi : -(u:ℂ)+(t:ℂ)*I =
      (-(u:ℂ)+(offset t:ℂ)*I)+(((2*Real.pi*(round (t/(2*Real.pi)):ℝ):ℂ))*I) := by
    unfold offset
    push_cast
    ring
  unfold ray
  rw [hi]
  simp only [Complex.exp_add, he, mul_one]

theorem full_angle_loss (u t : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000)
    (haway : ∀ k : ℤ, 3*u/4 ≤ |t-(k:ℝ)*(2*Real.pi)|) :
    (11/20)/u ≤ totalLoss (ray u t) := by
  have ha : 3*u/4 ≤ |offset t| := by
    simpa only [offset, mul_comm (round (t/(2*Real.pi)):ℝ) (2*Real.pi), mul_assoc]
      using haway (round (t/(2*Real.pi)))
  simpa only [ray_offset] using principal_loss u (offset t) hu hU ha (offset_bound t)

theorem full_angle_decay (u t : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000)
    (haway : ∀ k : ℤ, 3*u/4 ≤ |t-(k:ℝ)*(2*Real.pi)|) :
    ‖(EndpointEta.euler (ray u t))⁻¹‖ ≤
      ‖(EndpointEta.euler (Real.exp (-u):ℂ))⁻¹‖*Real.exp (-(11/20)/u) := by
  have hq : ‖ray u t‖ < 1 := by
    rw [ray_norm]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  simpa only [ray_norm, neg_div] using
    norm_decay (ray u t) hq ((11/20)/u) (full_angle_loss u t hu hU haway)

end
end Borwein.InverseEulerAngularDecay
