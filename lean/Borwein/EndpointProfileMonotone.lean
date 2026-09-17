import Borwein.EndpointScaledBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

namespace Borwein.EndpointProfileMonotone
noncomputable section
open Set EndpointScaledBounds

def poly2 (s : ℝ) : ℝ := Real.exp (-s)*(1+s+s^2/2)
def poly3 (s : ℝ) : ℝ := Real.exp (-s)*(1+s+s^2/2+s^3/6)

theorem poly2_deriv (s : ℝ) : HasDerivAt poly2 (-(s^2/2)*Real.exp (-s)) s := by
  have hi := hasDerivAt_id s
  have hp := ((hi.const_add 1).add ((hi.pow 2).div_const 2))
  convert! hi.neg.exp.mul hp using 1 <;> simp only [poly2, Pi.neg_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;> ring

theorem poly3_deriv (s : ℝ) : HasDerivAt poly3 (-(s^3/6)*Real.exp (-s)) s := by
  have hi := hasDerivAt_id s
  have hp := (((hi.const_add 1).add ((hi.pow 2).div_const 2)).add ((hi.pow 3).div_const 6))
  convert! hi.neg.exp.mul hp using 1 <;> simp only [poly3, Pi.neg_apply, Pi.add_apply, Pi.pow_apply, id_eq] <;> ring

theorem poly2_antitone : AntitoneOn poly2 (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (continuous_iff_continuousAt.mpr (fun s => (poly2_deriv s).continuousAt)).continuousOn
    (fun s _ => (poly2_deriv s).differentiableAt.differentiableWithinAt)
  intro s hs
  rw [(poly2_deriv s).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.exp_pos _).le

theorem poly3_antitone : AntitoneOn poly3 (Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (continuous_iff_continuousAt.mpr (fun s => (poly3_deriv s).continuousAt)).continuousOn
    (fun s _ => (poly3_deriv s).differentiableAt.differentiableWithinAt)
  intro s hs
  have hs0 : 0 ≤ s := interior_subset hs
  rw [(poly3_deriv s).deriv]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (Real.exp_pos _).le

theorem second_antitone (T τ : ℝ) (hT : 0 ≤ T) (hτ : T ≤ τ) (k : ℕ) :
    secondProfile τ k ≤ secondProfile T k := by
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
  have hh := poly2_antitone (show T*(k:ℝ) ∈ Ici 0 from mul_nonneg hT hk)
    (show τ*(k:ℝ) ∈ Ici 0 from mul_nonneg (hT.trans hτ) hk) (mul_le_mul_of_nonneg_right hτ hk)
  have hb := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (8/5)/(k:ℝ)^2)
  simp only [poly2, secondProfile, ← neg_mul] at hb ⊢
  convert! hb using 1 <;> ring

theorem third_antitone (T τ : ℝ) (hT : 0 ≤ T) (hτ : T ≤ τ) (k : ℕ) :
    thirdProfile τ k ≤ thirdProfile T k := by
  have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg _
  have hh := poly3_antitone (show T*(k:ℝ) ∈ Ici 0 from mul_nonneg hT hk)
    (show τ*(k:ℝ) ∈ Ici 0 from mul_nonneg (hT.trans hτ) hk) (mul_le_mul_of_nonneg_right hτ hk)
  have hb := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ) ≤ (24/5)/(k:ℝ)^2)
  simp only [poly3, thirdProfile, ← neg_mul] at hb ⊢
  convert! hb using 1 <;> ring

end
end Borwein.EndpointProfileMonotone
