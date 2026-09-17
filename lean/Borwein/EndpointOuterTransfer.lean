import Borwein.EndpointOuterNumericBudget

set_option autoImplicit false

namespace Borwein.EndpointOuterTransfer
noncomputable section
open Complex EndpointCircleKernel EndpointCircleFunctions EndpointGaussianIntegral EndpointActualPhase
  EndpointMainArcConnection EndpointOuterGeometry EndpointTailGlobalLog EndpointCoefficientConnection

/-- The still-required analytic estimate (5.11), exposed as an explicit hypothesis. -/
def GMinorBound (v : ℝ) : Prop := ∀ θ : ℝ, outside (width v) θ →
  ‖EndpointEta.G (point v θ)‖ ≤ 6*Real.exp (A/v-1/(25*v))

theorem kernel_norm (F : ℂ → ℂ) (m : ℕ) (v θ : ℝ) :
    ‖kernel F m v θ‖=‖F (point v θ)‖*Real.exp ((m:ℝ)*v) := by
  rw [kernel, norm_mul, Complex.norm_exp]
  simp

theorem exponential_budget (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    Real.exp (A/v-1/(25*v))*Real.exp (radialX n v/v)*Real.exp (k*v) ≤
      ‖center n k v‖*Real.exp (v/6)*Real.exp (-1/(30*v)) := by
  rw [EndpointRadialNormalization.center_norm n k v hn hv,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := EndpointSignedRadialLoss.radial_loss n v hn hv hτ
  have hg := div_le_div_of_nonneg_right (EndpointSignedRadialLoss.gap_budget n v hτ) hv.le
  have he : radialX n v/(5*v*(1-radialX n v))=(radialX n v/(5*(1-radialX n v)))/v := by field_simp
  rw [he] at hl
  rw [sub_div, sub_div] at hg
  have h1 : (1/30:ℝ)/v=1/(30*v) := by ring
  have h2 : (1/25:ℝ)/v=1/(25*v) := by ring
  rw [h1,h2] at hg
  rw [neg_div]
  linarith

theorem strong_pointwise (n m : ℕ) (v θ : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hG : GMinorBound v)
    (hθ : outside (width v) θ) :
    ‖kernel (EndpointCircleFunctions.polynomial n) m v θ‖ ≤
      (6/v)*‖center n (m:ℝ) v‖*Real.exp (v/6)*Real.exp (-1/(30*v)) := by
  have hq : ‖point v θ‖ < 1 := by rw [point_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hP := EndpointFiniteConnection.polynomial_eq_G_tail n (point v θ) hq
  have hT := EndpointSignedRadialLoss.tail_norm n (point v θ) v hn hv hV hτ (point_norm v θ)
  have hT' : ‖EndpointFiniteConnection.tail n (point v θ)‖ ≤ Real.exp (radialX n v/v)/v := by
    apply hT.trans
    apply (le_div_iff₀ hv).mpr
    nlinarith [Real.exp_pos (radialX n v/v)]
  rw [kernel_norm]
  change ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point v θ) (Borwein.polynomial n)‖*_ ≤ _
  rw [hP, norm_mul]
  calc
    _ ≤ (6*Real.exp (A/v-1/(25*v)))*(Real.exp (radialX n v/v)/v)*Real.exp ((m:ℝ)*v) := by gcongr; exact hG θ hθ
    _ = (6/v)*(Real.exp (A/v-1/(25*v))*Real.exp (radialX n v/v)*Real.exp ((m:ℝ)*v)) := by ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (exponential_budget n (m:ℝ) v hn hv hτ) (by positivity : 0 ≤ 6/v)
      simpa only [mul_assoc] using hh

theorem weak_pointwise (n m : ℕ) (v θ : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hG : GMinorBound v)
    (hθ : outside (width v) θ) :
    ‖kernel (EndpointCircleFunctions.difference n) m v θ‖ ≤
      (6/v)*‖center n (shiftedIndex n m) v‖*Real.exp (v/6)*Real.exp (-1/(30*v)) := by
  have hq : ‖point v θ‖ < 1 := by rw [point_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hP := EndpointFiniteConnection.polynomial_eq_G_tail n (point v θ) hq
  have hd : EndpointCircleFunctions.difference n (point v θ)=
      EndpointEta.G (point v θ)*(EndpointFiniteConnection.tail n (point v θ)-1) := by
    unfold EndpointCircleFunctions.difference EndpointCircleFunctions.polynomial
    rw [hP]
    ring
  have hT := endpoint_tail_bound n (point v θ) v hn hv hV hτ (point_norm v θ)
  have hX := EndpointRadialNormalization.radialX_positive n v
  have hs : radialX n v*Real.exp ((m:ℝ)*v)=Real.exp (shiftedIndex n m*v) := by
    unfold radialX shiftedIndex
    rw [← Real.exp_add]
    congr 1
    ring
  rw [kernel_norm, hd, norm_mul]
  calc
    _ ≤ (6*Real.exp (A/v-1/(25*v)))*((radialX n v/v)*Real.exp (radialX n v/v))*Real.exp ((m:ℝ)*v) := by
      gcongr
      exact hG θ hθ
    _ = (6/v)*(Real.exp (A/v-1/(25*v))*Real.exp (radialX n v/v)*(radialX n v*Real.exp ((m:ℝ)*v))) := by ring
    _ = (6/v)*(Real.exp (A/v-1/(25*v))*Real.exp (radialX n v/v)*Real.exp (shiftedIndex n m*v)) := by rw [hs]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (exponential_budget n (shiftedIndex n m) v hn hv hτ) (by positivity : 0 ≤ 6/v)
      simpa only [mul_assoc] using hh

end
end Borwein.EndpointOuterTransfer
