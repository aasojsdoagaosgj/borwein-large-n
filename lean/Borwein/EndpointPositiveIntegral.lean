import Borwein.EndpointPositiveFinite

set_option autoImplicit false

namespace Borwein.EndpointPositiveIntegral
noncomputable section
open Complex MeasureTheory Set EndpointPhaseAtoms EndpointGaussianIntegral
  EndpointMainArcConnection EndpointPositiveFinite

def strongIntegral (n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  value n v y*exp ((k:ℂ)*coordinate v y)
def weakIntegral (n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  difference n v y*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)

theorem strong_integral_bound (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖strongIntegral n k v‖ ≤ 60*‖center n k v‖*Real.exp (-(9/10)/v) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(width v)) (b := width v)
    (f := fun y => value n v y*exp ((k:ℂ)*coordinate v y))
    (C := (40/v)*‖center n k v‖*Real.exp (-(9/10)/v)) (by
      intro y hy
      rw [uIoc_of_le (by unfold width; linarith : -(width v) ≤ width v)] at hy
      exact strong_pointwise n k v y hn hv hV (abs_le.mpr ⟨hy.1.le,hy.2⟩) hτ)
  apply hh.trans_eq
  have he : |width v-(-(width v))|=3*v/2 := by unfold width; rw [abs_of_pos (by linarith)]; ring
  rw [he]
  field_simp
  <;> ring

theorem weak_integral_bound (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖weakIntegral n k v‖ ≤ 60*‖center n k v‖*Real.exp (-(9/10)/v) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(width v)) (b := width v)
    (f := fun y => difference n v y*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y))
    (C := (40/v)*‖center n k v‖*Real.exp (-(9/10)/v)) (by
      intro y hy
      rw [uIoc_of_le (by unfold width; linarith : -(width v) ≤ width v)] at hy
      exact weak_pointwise n k v y hn hv hV (abs_le.mpr ⟨hy.1.le,hy.2⟩) hτ)
  apply hh.trans_eq
  have he : |width v-(-(width v))|=3*v/2 := by unfold width; rw [abs_of_pos (by linarith)]; ring
  rw [he]
  field_simp
  <;> ring

theorem strong_ratio_bound (a : Fin 3) (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖strongIntegral n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))‖ ≤ v := by
  apply EndpointEtaIntegral.ratio_bound n k v _ _ hn hv hV hτ _ (strong_integral_bound n k v hn hv hV hτ)
  rw [norm_mul]
  have hh := EndpointStrongConstants.constant_norm_lower a
  nlinarith [norm_nonneg (center n k v)]

theorem weak_ratio_bound (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖weakIntegral n k v/((-center n k v)*(normalizer n v:ℂ))‖ ≤ v := by
  apply EndpointEtaIntegral.ratio_bound n k v _ _ hn hv hV hτ _ (weak_integral_bound n k v hn hv hV hτ)
  simp only [norm_neg, le_refl]

end
end Borwein.EndpointPositiveIntegral
