import Borwein.EndpointOuterTransfer

set_option autoImplicit false

namespace Borwein.EndpointOuterIntegral
noncomputable section
open Complex EndpointCircleKernel EndpointGaussianIntegral EndpointMainArcConnection
  EndpointOuterTransfer EndpointOuterGeometry EndpointCirclePartition EndpointCoefficientConnection

theorem width_valid (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) : 0 ≤ width v ∧ width v ≤ Real.pi/5 := by
  unfold width
  constructor <;> nlinarith [Real.pi_gt_d2]

theorem strong_outer_bound (n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hG : GMinorBound v) :
    ‖strongOuter n m v‖ ≤ (12*Real.pi/v)*‖center n (m:ℝ) v‖*Real.exp (v/6)*Real.exp (-1/(30*v)) := by
  have hh := outer_integral_bound (kernel (EndpointCircleFunctions.polynomial n) m v)
    ((6/v)*‖center n (m:ℝ) v‖*Real.exp (v/6)*Real.exp (-1/(30*v))) (width v)
    (by positivity) (width_valid v hv hV).1 (width_valid v hv hV).2
    (fun θ hθ => strong_pointwise n m v θ hn hv hV hτ hG hθ)
  exact hh.trans_eq (by ring)

theorem weak_outer_bound (n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hG : GMinorBound v) :
    ‖weakOuter n m v‖ ≤ (12*Real.pi/v)*‖center n (shiftedIndex n m) v‖*Real.exp (v/6)*Real.exp (-1/(30*v)) := by
  have hh := outer_integral_bound (kernel (EndpointCircleFunctions.difference n) m v)
    ((6/v)*‖center n (shiftedIndex n m) v‖*Real.exp (v/6)*Real.exp (-1/(30*v))) (width v)
    (by positivity) (width_valid v hv hV).1 (width_valid v hv hV).2
    (fun θ hθ => weak_pointwise n m v θ hn hv hV hτ hG hθ)
  exact hh.trans_eq (by ring)

theorem ratio_bound (n : ℕ) (k v : ℝ) (z c : ℂ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hc : ‖center n k v‖ ≤ ‖c‖)
    (hz : ‖z‖ ≤ (12*Real.pi/v)*‖center n k v‖*Real.exp (v/6)*Real.exp (-1/(30*v))) :
    ‖z/(c*(normalizer n v:ℂ))‖ ≤ (1/5:ℝ) := by
  have hJ := normalizer_pos n v hn hv
  have hC : 0 < ‖c‖ := (norm_pos_iff.mpr (center_ne_zero n k v)).trans_le hc
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hJ.le]
  calc
    _ ≤ ((12*Real.pi/v)*‖center n k v‖*Real.exp (v/6)*Real.exp (-1/(30*v)))/(‖c‖*normalizer n v) :=
      div_le_div_of_nonneg_right hz (by positivity)
    _ ≤ ((12*Real.pi/v)*‖c‖*Real.exp (v/6)*Real.exp (-1/(30*v)))/(‖c‖*normalizer n v) := by gcongr
    _ = ((12*Real.pi*Real.exp (v/6))/(v*normalizer n v))*Real.exp (-1/(30*v)) := by
      field_simp
      <;> ring
    _ ≤ _ := EndpointOuterNumericBudget.outer_budget n v hn hv hV hτ

theorem strong_ratio_bound (a : Fin 3) (n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hG : GMinorBound v) :
    ‖strongOuter n m v/(EndpointRootCancellation.constant a.val*center n (m:ℝ) v*(normalizer n v:ℂ))‖ ≤ (1/5:ℝ) := by
  apply ratio_bound n (m:ℝ) v _ _ hn hv hV hτ _ (strong_outer_bound n m v hn hv hV hτ hG)
  rw [norm_mul]
  have hh := EndpointStrongConstants.constant_norm_lower a
  nlinarith [norm_nonneg (center n (m:ℝ) v)]

theorem weak_ratio_bound (n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hG : GMinorBound v) :
    ‖weakOuter n m v/((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))‖ ≤ (1/5:ℝ) := by
  apply ratio_bound n (shiftedIndex n m) v _ _ hn hv hV hτ _ (weak_outer_bound n m v hn hv hV hτ hG)
  simp only [norm_neg, le_refl]

end
end Borwein.EndpointOuterIntegral
