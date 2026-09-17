import Borwein.EulerWeakFilter
import Borwein.EndpointConditionalSign

set_option autoImplicit false

namespace Borwein.EndpointWeakIntegralZero
noncomputable section
open Complex MeasureTheory FivePoleCircle EndpointEta EndpointCircleKernel EndpointCircleFunctions
  EndpointCoefficientConnection EndpointOuterTransfer EndpointGaussianIntegral EndpointMainArcConnection

theorem shifted_point (j : ℕ) (v θ : ℝ) :
    point v (θ+angle j)=zeta^j*point v θ := by
  rw [← root_angle, point, point, ← exp_add]
  congr 1
  push_cast
  ring

theorem shifted_kernel (j m : ℕ) (v θ : ℝ) :
    kernel G m v (θ+angle j)=zeta^(-(((m%5)*j:ℕ):ℤ))*G (zeta^j*point v θ)*
      exp ((m:ℂ)*((v:ℂ)-(θ:ℂ)*I)) := by
  rw [kernel, shifted_point]
  have he : (m:ℂ)*((v:ℂ)-((θ+angle j:ℝ):ℂ)*I)=
      -(m:ℂ)*(angle j:ℂ)*I+(m:ℂ)*((v:ℂ)-(θ:ℂ)*I) := by push_cast; ring
  rw [he, exp_add, phase_weight]
  ring

theorem shifted_sum_zero (m : ℕ) (v θ : ℝ) (hv : 0 < v) (hm : m%5=3 ∨ m%5=4) :
    (∑ j : Fin 5, kernel G m v (θ+angle j.val))=0 := by
  have hq : ‖point v θ‖ < 1 := by rw [point_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : point v θ ≠ 0 := exp_ne_zero _
  simp_rw [shifted_kernel]
  rw [← Finset.sum_mul, EulerWeakFilter.G_filter_zero (point v θ) (m%5) hq hq0 hm, zero_mul]

theorem integral_shift (f : ℝ → ℂ) (c : ℝ) (hf : Function.Periodic f (2*Real.pi)) :
    (∫ θ in (0:ℝ)..2*Real.pi, f (θ+c))=∫ θ in (0:ℝ)..2*Real.pi, f θ := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_zero, add_comm] using hf.intervalIntegral_add_eq c 0

/-- The actual coefficient integral of G vanishes in both weak residue classes. -/
theorem GIntegral_zero (m : ℕ) (v : ℝ) (hv : 0 < v) (hm : m%5=3 ∨ m%5=4) :
    GIntegral m v=0 := by
  have hC := kernel_continuous G m v (G_continuous v hv)
  have hi (j : Fin 5) : IntervalIntegrable (fun θ => kernel G m v (θ+angle j.val))
      volume 0 (2*Real.pi) :=
    (hC.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have hz : (∫ θ in (0:ℝ)..2*Real.pi, ∑ j : Fin 5, kernel G m v (θ+angle j.val))=0 := by
    simp_rw [shifted_sum_zero m v _ hv hm]
    exact intervalIntegral.integral_zero
  rw [intervalIntegral.integral_finset_sum (fun j _ => hi j)] at hz
  simp_rw [integral_shift (kernel G m v) _ (kernel_periodic G m v)] at hz
  change (∑ _j : Fin 5, GIntegral m v)=0 at hz
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- The previously separate GIntegral=0 input is discharged for the endpoint budget. -/
theorem weak_budget (a n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=shiftedIndex n m/(5*(n:ℝ)^2))
    (hG : GMinorBound v) :
    ‖(((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))/
      ((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))-1‖ ≤ (177/200:ℝ) := by
  apply EndpointConditionalSign.weak_budget a n m v hn hv hV hτ ha hA hs hG
  exact GIntegral_zero m v hv (by rw [ha]; exact hA)

/-- Only the minor-arc estimate and endpoint/saddle conditions remain as analytic inputs. -/
theorem weak_sign (a n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=shiftedIndex n m/(5*(n:ℝ)^2))
    (hG : GMinorBound v) : (Borwein.polynomial n).coeff m < 0 := by
  apply EndpointConditionalSign.weak_sign a n m v hn hv hV hτ ha hA hs hG
  exact GIntegral_zero m v hv (by rw [ha]; exact hA)

end
end Borwein.EndpointWeakIntegralZero
