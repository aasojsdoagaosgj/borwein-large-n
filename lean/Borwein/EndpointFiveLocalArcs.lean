import Borwein.EndpointPositiveIntegral
import Borwein.EndpointPositiveContinuity

set_option autoImplicit false

namespace Borwein.EndpointFiveLocalArcs
noncomputable section
open Complex MeasureTheory EndpointPhaseAtoms EndpointGaussianIntegral EndpointMainArcConnection
  EndpointPositiveFinite EndpointPositiveContinuity EndpointPolynomialContinuity

def fiveValue (a n : ℕ) (v y : ℝ) : ℂ := ∑ j : Fin 5,
  FivePoleCircle.zeta^(-((a*j.val:ℕ):ℤ))*Polynomial.eval₂ (Int.castRingHom ℂ)
    (FivePoleCircle.zeta^j.val*exp (-coordinate v y)) (Borwein.polynomial n)
def fiveDifference (a n : ℕ) (v y : ℝ) : ℂ := ∑ j : Fin 5,
  FivePoleCircle.zeta^(-((a*j.val:ℕ):ℤ))*(Polynomial.eval₂ (Int.castRingHom ℂ)
    (FivePoleCircle.zeta^j.val*exp (-coordinate v y)) (Borwein.polynomial n)-
      EndpointEta.G (FivePoleCircle.zeta^j.val*exp (-coordinate v y)))
def strongIntegral (a : Fin 3) (n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  fiveValue a.val n v y*exp ((k:ℂ)*coordinate v y)
def weakIntegral (a n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  fiveDifference a n v y*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)

theorem fiveValue_split (a n : ℕ) (v y : ℝ) :
    fiveValue a n v y=value n v y+EndpointStrongPolynomial.polynomialSum a n (coordinate v y) := by
  unfold fiveValue
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.cast_zero, neg_zero, zpow_zero, pow_zero, one_mul]
  rfl

theorem fiveDifference_split (a n : ℕ) (v y : ℝ) :
    fiveDifference a n v y=difference n v y+EndpointWeakPolynomial.polynomialDifference a n (coordinate v y) := by
  unfold fiveDifference
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.mul_zero, Nat.cast_zero, neg_zero, zpow_zero, pow_zero, one_mul]
  rfl

theorem strong_decomposition (a : Fin 3) (n : ℕ) (k v : ℝ) :
    strongIntegral a n k v=EndpointPositiveIntegral.strongIntegral n k v+EndpointFiniteLocalArc.strongIntegral a n k v := by
  have hE : Continuous (fun y : ℝ => exp ((k:ℂ)*coordinate v y)) := by unfold coordinate; fun_prop
  have hP : Continuous (fun y => value n v y*exp ((k:ℂ)*coordinate v y)) := (value_continuous n v).mul hE
  have hF : Continuous (fun y => EndpointStrongPolynomial.polynomialSum a.val n (coordinate v y)*exp ((k:ℂ)*coordinate v y)) :=
    (polynomialSum_continuous a.val n v).mul hE
  unfold strongIntegral EndpointPositiveIntegral.strongIntegral EndpointFiniteLocalArc.strongIntegral
  rw [← intervalIntegral.integral_add (hP.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [fiveValue_split]
  ring

theorem weak_decomposition (a n : ℕ) (k v : ℝ) (hv : 0 < v) :
    weakIntegral a n k v=EndpointPositiveIntegral.weakIntegral n k v+EndpointFiniteLocalArc.weakIntegral a n k v := by
  have hE : Continuous (fun y : ℝ => exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)) := by unfold coordinate; fun_prop
  have hP : Continuous (fun y => difference n v y*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)) :=
    (difference_continuous n v hv).mul hE
  have hF : Continuous (fun y => EndpointWeakPolynomial.polynomialDifference a n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)) :=
    (polynomialDifference_continuous a n v hv).mul hE
  unfold weakIntegral EndpointPositiveIntegral.weakIntegral EndpointFiniteLocalArc.weakIntegral
  rw [← intervalIntegral.integral_add (hP.intervalIntegrable _ _) (hF.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [fiveDifference_split]
  ring

theorem strong_normalized_bound (a : Fin 3) (n : ℕ) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖strongIntegral a n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+62*v := by
  rw [strong_decomposition a n k v, add_div]
  have he : ∀ z t : ℂ, z+t-1=z+(t-1) := by intros; ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hp := EndpointPositiveIntegral.strong_ratio_bound a n k v hn hv hV hτ
  have hf := EndpointFiniteLocalArc.strong_normalized_bound a n k v hn hv hV hτ hs
  linarith

theorem weak_normalized_bound (a n : ℕ) (ha : a=3 ∨ a=4) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+62*v := by
  rw [weak_decomposition a n k v hv, add_div]
  have he : ∀ z t : ℂ, z+t-1=z+(t-1) := by intros; ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hp := EndpointPositiveIntegral.weak_ratio_bound n k v hn hv hV hτ
  have hf := EndpointFiniteLocalArc.weak_normalized_bound a n ha k v hn hv hV hτ hs
  linarith

theorem strong_uniform_budget (a : Fin 3) (n : ℕ) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖strongIntegral a n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))-1‖ ≤ (685/1000:ℝ) := by
  have hh := strong_normalized_bound a n k v hn hv hV hτ hs
  have hb := EndpointLocalNumericBudget.uniform_budget n v hv hV hτ
  linarith

theorem weak_uniform_budget (a n : ℕ) (ha : a=3 ∨ a=4) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))-1‖ ≤ (685/1000:ℝ) := by
  have hh := weak_normalized_bound a n ha k v hn hv hV hτ hs
  have hb := EndpointLocalNumericBudget.uniform_budget n v hv hV hτ
  linarith

end
end Borwein.EndpointFiveLocalArcs
