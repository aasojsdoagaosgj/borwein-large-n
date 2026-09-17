import Borwein.EndpointCircleFunctions

set_option autoImplicit false

namespace Borwein.EndpointCoefficientConnection
noncomputable section
open Complex MeasureTheory EndpointCircleKernel EndpointCirclePartition EndpointCircleFunctions
  EndpointGaussianIntegral EndpointMainArcConnection

def strongOuter (n m : ℕ) (v : ℝ) : ℂ := outerSum (kernel (EndpointCircleFunctions.polynomial n) m v) (width v)
def weakOuter (n m : ℕ) (v : ℝ) : ℂ := outerSum (kernel (difference n) m v) (width v)
def shiftedIndex (n m : ℕ) : ℝ := (m:ℝ)-((5*n:ℕ):ℝ)

theorem strong_local (a : Fin 3) (n m : ℕ) (v : ℝ) (ha : m%5=a.val) :
    localSum (kernel (EndpointCircleFunctions.polynomial n) m v) (width v)=EndpointFiveLocalArcs.strongIntegral a n (m:ℝ) v := by
  rw [local_weighted (EndpointCircleFunctions.polynomial n) m v (width v) (polynomial_continuous n v)]
  rw [ha]
  rfl

theorem weak_local (a n m : ℕ) (v : ℝ) (hv : 0 < v) (ha : m%5=a) :
    localSum (kernel (difference n) m v) (width v)=EndpointFiveLocalArcs.weakIntegral a n (shiftedIndex n m) v := by
  rw [local_weighted (difference n) m v (width v) (difference_continuous n v hv), ha]
  have he : shiftedIndex n m+((5*n:ℕ):ℝ)=(m:ℝ) := by unfold shiftedIndex; ring
  unfold EndpointFiveLocalArcs.weakIntegral
  rw [he]
  rfl

theorem strong_coefficient_split (a : Fin 3) (n m : ℕ) (v : ℝ) (ha : m%5=a.val) :
    ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ)=
      EndpointFiveLocalArcs.strongIntegral a n (m:ℝ) v+strongOuter n m v := by
  have hp := full_partition (kernel (EndpointCircleFunctions.polynomial n) m v)
    (kernel_continuous (EndpointCircleFunctions.polynomial n) m v (polynomial_continuous n v)) (kernel_periodic _ _ _) (width v)
  have hi : (∫ θ in (0:ℝ)..2*Real.pi, kernel (EndpointCircleFunctions.polynomial n) m v θ)=
      ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ) := polynomial_integral (Borwein.polynomial n) m v
  rw [hi, strong_local a n m v ha] at hp
  exact hp

theorem weak_coefficient_split (a n m : ℕ) (v : ℝ) (hv : 0 < v) (ha : m%5=a) :
    ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ)=
      EndpointFiveLocalArcs.weakIntegral a n (shiftedIndex n m) v+weakOuter n m v+GIntegral m v := by
  have hp := full_partition (kernel (difference n) m v)
    (kernel_continuous (difference n) m v (difference_continuous n v hv)) (kernel_periodic _ _ _) (width v)
  rw [difference_integral n m v hv, weak_local a n m v hv ha] at hp
  change _ = _+weakOuter n m v at hp
  linear_combination hp

theorem strong_coefficient_error (a : Fin 3) (n m : ℕ) (v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (ha : m%5=a.val) (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=(m:ℝ)/(5*(n:ℝ)^2)) :
    ‖(((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))/
        (EndpointRootCancellation.constant a.val*center n (m:ℝ) v*(normalizer n v:ℂ))-1‖ ≤
      (685/1000:ℝ)+‖strongOuter n m v/(EndpointRootCancellation.constant a.val*center n (m:ℝ) v*(normalizer n v:ℂ))‖ := by
  rw [strong_coefficient_split a n m v ha, add_div]
  have he : ∀ z t : ℂ, z+t-1=(z-1)+t := by intros; ring
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (EndpointFiveLocalArcs.strong_uniform_budget a n (m:ℝ) v hn hv hV hτ hs) le_rfl)

theorem weak_coefficient_error (a n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=shiftedIndex n m/(5*(n:ℝ)^2)) :
    ‖(((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))/((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))-1‖ ≤
      (685/1000:ℝ)+‖weakOuter n m v/((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))‖+
        ‖GIntegral m v/((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))‖ := by
  rw [weak_coefficient_split a n m v hv ha, add_div, add_div]
  have ht (z t u : ℂ) : ‖z+t+u-1‖ ≤ ‖z-1‖+‖t‖+‖u‖ := by
    have he : z+t+u-1=(z-1)+t+u := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  apply (ht _ _ _).trans
  have hb := EndpointFiveLocalArcs.weak_uniform_budget a n hA (shiftedIndex n m) v hn hv hV hτ hs
  linarith

theorem weak_coefficient_error_of_G_zero (a n m : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=shiftedIndex n m/(5*(n:ℝ)^2))
    (hG : GIntegral m v=0) :
    ‖(((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ))/((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))-1‖ ≤
      (685/1000:ℝ)+‖weakOuter n m v/((-center n (shiftedIndex n m) v)*(normalizer n v:ℂ))‖ := by
  simpa only [hG, zero_div, norm_zero, add_zero] using weak_coefficient_error a n m v hn hv hV hτ ha hA hs

end
end Borwein.EndpointCoefficientConnection
