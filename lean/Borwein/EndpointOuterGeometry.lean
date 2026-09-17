import Borwein.EndpointCirclePartition

set_option autoImplicit false

namespace Borwein.EndpointOuterGeometry
noncomputable section
open Complex Set MeasureTheory EndpointCircleKernel EndpointCirclePartition

def outside (h θ : ℝ) : Prop := ∀ k : ℤ, h ≤ |θ-2*Real.pi*(k:ℝ)/5|

theorem right_outside (j : ℕ) (h θ : ℝ) (hh : h ≤ Real.pi/5)
    (hθ : θ ∈ Icc (angle j+h) (boundary (j+1))) : outside h θ := by
  intro k
  rw [boundary_right] at hθ
  by_cases hk : k ≤ (j:ℤ)
  · have hc : (k:ℝ) ≤ (j:ℝ) := by exact_mod_cast hk
    have ha : 2*Real.pi*(k:ℝ)/5 ≤ angle j := by unfold angle; gcongr
    have hb := le_abs_self (θ-2*Real.pi*(k:ℝ)/5)
    linarith [hθ.1]
  · have hc : (j:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast (show (j:ℤ)+1 ≤ k by omega)
    have ha : angle j+2*Real.pi/5 ≤ 2*Real.pi*(k:ℝ)/5 := by
      calc
        _ = 2*Real.pi*((j:ℝ)+1)/5 := by unfold angle; ring
        _ ≤ _ := by gcongr
    have hb := neg_le_abs (θ-2*Real.pi*(k:ℝ)/5)
    linarith [hθ.2]

theorem left_outside (j : ℕ) (h θ : ℝ) (hh : h ≤ Real.pi/5)
    (hθ : θ ∈ Icc (boundary j) (angle j-h)) : outside h θ := by
  intro k
  rw [boundary_left] at hθ
  by_cases hk : (j:ℤ) ≤ k
  · have hc : (j:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have ha : angle j ≤ 2*Real.pi*(k:ℝ)/5 := by unfold angle; gcongr
    have hb := neg_le_abs (θ-2*Real.pi*(k:ℝ)/5)
    linarith [hθ.2]
  · have hc : (k:ℝ)+1 ≤ (j:ℝ) := by exact_mod_cast (show k+1 ≤ (j:ℤ) by omega)
    have ha : 2*Real.pi*(k:ℝ)/5+2*Real.pi/5 ≤ angle j := by
      calc
        _ = 2*Real.pi*((k:ℝ)+1)/5 := by ring
        _ ≤ _ := by unfold angle; gcongr
    have hb := le_abs_self (θ-2*Real.pi*(k:ℝ)/5)
    linarith [hθ.1]

theorem left_integral_bound (f : ℝ → ℂ) (B h : ℝ) (hh : h ≤ Real.pi/5)
    (hb : ∀ θ, outside h θ → ‖f θ‖ ≤ B) (j : ℕ) :
    ‖∫ θ in boundary j..angle j-h, f θ‖ ≤ B*(Real.pi/5-h) := by
  have hO : boundary j ≤ angle j-h := by rw [boundary_left]; linarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := boundary j) (b := angle j-h) (f := f) (C := B) (by
      intro θ hθ
      rw [uIoc_of_le hO] at hθ
      exact hb θ (left_outside j h θ hh ⟨hθ.1.le,hθ.2⟩))
  apply hi.trans_eq
  rw [abs_of_nonneg (sub_nonneg.mpr hO), boundary_left]
  ring

theorem right_integral_bound (f : ℝ → ℂ) (B h : ℝ) (hh : h ≤ Real.pi/5)
    (hb : ∀ θ, outside h θ → ‖f θ‖ ≤ B) (j : ℕ) :
    ‖∫ θ in angle j+h..boundary (j+1), f θ‖ ≤ B*(Real.pi/5-h) := by
  have hO : angle j+h ≤ boundary (j+1) := by rw [boundary_right]; linarith
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := angle j+h) (b := boundary (j+1)) (f := f) (C := B) (by
      intro θ hθ
      rw [uIoc_of_le hO] at hθ
      exact hb θ (right_outside j h θ hh ⟨hθ.1.le,hθ.2⟩))
  apply hi.trans_eq
  rw [abs_of_nonneg (sub_nonneg.mpr hO), boundary_right]
  ring

theorem outer_integral_bound (f : ℝ → ℂ) (B h : ℝ) (hB : 0 ≤ B) (h0 : 0 ≤ h) (hh : h ≤ Real.pi/5)
    (hb : ∀ θ, outside h θ → ‖f θ‖ ≤ B) : ‖outerSum f h‖ ≤ 2*Real.pi*B := by
  unfold outerSum
  apply (norm_sum_le _ _).trans
  have hs : (∑ j : Fin 5, ‖(∫ θ in boundary j.val..angle j.val-h, f θ)+
      (∫ θ in angle j.val+h..boundary (j.val+1), f θ)‖) ≤
      ∑ _j : Fin 5, 2*B*(Real.pi/5-h) := by
    apply Finset.sum_le_sum
    intro j _
    have hl := left_integral_bound f B h hh hb j.val
    have hr := right_integral_bound f B h hh hb j.val
    exact (norm_add_le _ _).trans (by linarith)
  apply hs.trans
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith

end
end Borwein.EndpointOuterGeometry
