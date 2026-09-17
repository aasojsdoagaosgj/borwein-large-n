import Borwein.EndpointLocalAmplitudeIntegral

set_option autoImplicit false

namespace Borwein.EndpointMainArcConnection
noncomputable section
open Complex MeasureTheory EndpointPhaseAtoms EndpointSaddleEnergy EndpointTaylor
  EndpointGaussianIntegral EndpointAmplitudeContinuity EndpointAmplitudeBudget

def center (n : ℕ) (k v : ℝ) : ℂ := exp (energy n k v 0-(v:ℂ)/6)
def strongIntegral (a : Fin 3) (n : ℕ) (k v : ℝ) : ℂ :=
  ∫ y in -(width v)..width v,
    EndpointStrongPolynomial.mainTail a.val n (coordinate v y)*exp ((k:ℂ)*coordinate v y)
def weakIntegral (a n : ℕ) (k v : ℝ) : ℂ :=
  ∫ y in -(width v)..width v,
    EndpointWeakTail.filteredMain a n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)

theorem center_ne_zero (n : ℕ) (k v : ℝ) : center n k v ≠ 0 := exp_ne_zero _

theorem center_real (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    center n k v=((Real.exp ((n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)+k*v-v/6):ℝ):ℂ) := by
  rw [center, energy_zero n k v hn hv]
  push_cast
  rfl

theorem common_exponential (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*coordinate v y)-coordinate v y/6)*
      exp ((k:ℂ)*coordinate v y) = center n k v*exp (phase n v y)*rotation y := by
  have he := energy_difference n k v y hn hv hs
  rw [actual_energy n k v y hn hv] at he
  unfold center rotation
  rw [← exp_add, ← exp_add, ← exp_add]
  congr 1
  rw [← he]
  unfold coordinate
  ring

theorem strong_integrand (a : Fin 3) (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    EndpointStrongPolynomial.mainTail a.val n (coordinate v y)*exp ((k:ℂ)*coordinate v y) =
      (EndpointRootCancellation.constant a.val*center n k v)*
        (exp (phase n v y)*adjusted (strongError a n v) y) := by
  have hl : EndpointStrongPolynomial.mainTail a.val n (coordinate v y) =
      EndpointStrongPolynomial.leading a n (coordinate v y)*(1+strongError a n v y) := by
    unfold strongError
    field_simp [EndpointStrongPolynomial.leading_ne_zero]
    ring
  rw [hl]
  unfold EndpointStrongPolynomial.leading adjusted
  calc
    _ = EndpointRootCancellation.constant a.val*
        (exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*coordinate v y)-coordinate v y/6)*
          exp ((k:ℂ)*coordinate v y))*(1+strongError a n v y) := by ring
    _ = _ := by rw [common_exponential n k v y hn hv hs]; ring

theorem weak_integrand (a n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    EndpointWeakTail.filteredMain a n (coordinate v y)*
        exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y) =
      (-center n k v)*(exp (phase n v y)*adjusted (weakError a n v) y) := by
  have hl : EndpointWeakTail.filteredMain a n (coordinate v y) =
      EndpointWeakTail.weakLeading n (coordinate v y)*(1+weakError a n v y) := by
    unfold weakError
    field_simp [EndpointWeakTail.weakLeading_ne_zero]
    ring
  have hx : EndpointSharpTail.x n (coordinate v y)*
      exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)=exp ((k:ℂ)*coordinate v y) := by
    unfold EndpointSharpTail.x
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [hl]
  unfold EndpointWeakTail.weakLeading adjusted
  calc
    _ = -(exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*coordinate v y)-coordinate v y/6)*
        (EndpointSharpTail.x n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)))*
        (1+weakError a n v y) := by ring
    _ = _ := by rw [hx, common_exponential n k v y hn hv hs]; ring

theorem strong_integral_eq (a : Fin 3) (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    strongIntegral a n k v=(EndpointRootCancellation.constant a.val*center n k v)*
      EndpointLocalAmplitudeIntegral.integral n v (strongError a n v) := by
  unfold strongIntegral EndpointLocalAmplitudeIntegral.integral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  exact strong_integrand a n k v y hn hv hs

theorem weak_integral_eq (a n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    weakIntegral a n k v=(-center n k v)*
      EndpointLocalAmplitudeIntegral.integral n v (weakError a n v) := by
  unfold weakIntegral EndpointLocalAmplitudeIntegral.integral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro y _
  exact weak_integrand a n k v y hn hv hs

theorem strong_normalized_bound (a : Fin 3) (n : ℕ) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖strongIntegral a n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+60*v := by
  rw [strong_integral_eq a n k v hn hv hs, mul_div_mul_left _ _
    (mul_ne_zero (EndpointStrongConstants.constant_ne_zero a) (center_ne_zero n k v))]
  exact EndpointLocalAmplitudeIntegral.strong_normalized_bound a n v hn hv hV hτ

theorem weak_normalized_bound (a n : ℕ) (ha : a=3 ∨ a=4) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+60*v := by
  rw [weak_integral_eq a n k v hn hv hs, mul_div_mul_left _ _ (neg_ne_zero.mpr (center_ne_zero n k v))]
  exact EndpointLocalAmplitudeIntegral.weak_normalized_bound a n ha v hn hv hV hτ

end
end Borwein.EndpointMainArcConnection
