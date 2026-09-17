import Borwein.EndpointEtaIntegral

set_option autoImplicit false

namespace Borwein.EndpointFiniteLocalArc
noncomputable section
open Complex MeasureTheory EndpointPhaseAtoms EndpointGaussianIntegral EndpointMainArcConnection
  EndpointPolynomialContinuity EndpointAmplitudeContinuity

def strongIntegral (a : Fin 3) (n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  EndpointStrongPolynomial.polynomialSum a.val n (coordinate v y)*exp ((k:ℂ)*coordinate v y)
def weakIntegral (a n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  EndpointWeakPolynomial.polynomialDifference a n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)

theorem strong_decomposition (a : Fin 3) (n : ℕ) (k v : ℝ) (hv : 0 < v) :
    strongIntegral a n k v=EndpointMainArcConnection.strongIntegral a n k v+EndpointEtaIntegral.strongIntegral a.val n k v := by
  have hE : Continuous (fun y : ℝ => exp ((k:ℂ)*coordinate v y)) := by unfold coordinate; fun_prop
  have hM : Continuous (fun y => EndpointStrongPolynomial.mainTail a.val n (coordinate v y)*exp ((k:ℂ)*coordinate v y)) :=
    (mainTail_continuous a.val n v hv).mul hE
  have hT : Continuous (fun y => EndpointStrongPolynomial.strongEta a.val n (coordinate v y)*exp ((k:ℂ)*coordinate v y)) :=
    (strongEta_continuous a.val n v hv).mul hE
  unfold strongIntegral EndpointMainArcConnection.strongIntegral EndpointEtaIntegral.strongIntegral
  rw [← intervalIntegral.integral_add (hM.intervalIntegrable _ _) (hT.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [EndpointStrongPolynomial.polynomial_decomposition a.val n _ (by simpa [coordinate] using hv)]
  ring

theorem weak_decomposition (a n : ℕ) (k v : ℝ) (hv : 0 < v) :
    weakIntegral a n k v=EndpointMainArcConnection.weakIntegral a n k v+EndpointEtaIntegral.weakIntegral a n k v := by
  have hE : Continuous (fun y : ℝ => exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)) := by unfold coordinate; fun_prop
  have hM : Continuous (fun y => EndpointWeakTail.filteredMain a n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)) :=
    (filteredMain_continuous a n v hv).mul hE
  have hT : Continuous (fun y => EndpointWeakPolynomial.etaRemainder a n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)) :=
    (etaRemainder_continuous a n v hv).mul hE
  unfold weakIntegral EndpointMainArcConnection.weakIntegral EndpointEtaIntegral.weakIntegral
  rw [← intervalIntegral.integral_add (hM.intervalIntegrable _ _) (hT.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [EndpointWeakPolynomial.polynomial_decomposition a n _ (by simpa [coordinate] using hv)]
  ring

theorem strong_normalized_bound (a : Fin 3) (n : ℕ) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖strongIntegral a n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+61*v := by
  rw [strong_decomposition a n k v hv, add_div]
  have he : ∀ z t : ℂ, z+t-1=(z-1)+t := by intros; ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hm := EndpointMainArcConnection.strong_normalized_bound a n k v hn hv hV hτ hs
  have ht := EndpointEtaIntegral.strong_ratio_bound a n k v hn hv hV hτ
  linarith

theorem weak_normalized_bound (a n : ℕ) (ha : a=3 ∨ a=4) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+61*v := by
  rw [weak_decomposition a n k v hv, add_div]
  have he : ∀ z t : ℂ, z+t-1=(z-1)+t := by intros; ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hm := EndpointMainArcConnection.weak_normalized_bound a n ha k v hn hv hV hτ hs
  have ht := EndpointEtaIntegral.weak_ratio_bound a n k v hn hv hV hτ
  linarith

theorem strong_uniform_budget (a : Fin 3) (n : ℕ) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖strongIntegral a n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))-1‖ ≤ (683/1000:ℝ) := by
  have hh := strong_normalized_bound a n k v hn hv hV hτ hs
  have hb := EndpointLocalNumericBudget.uniform_budget n v hv hV hτ
  linarith

theorem weak_uniform_budget (a n : ℕ) (ha : a=3 ∨ a=4) (k v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))-1‖ ≤ (683/1000:ℝ) := by
  have hh := weak_normalized_bound a n ha k v hn hv hV hτ hs
  have hb := EndpointLocalNumericBudget.uniform_budget n v hv hV hτ
  linarith

end
end Borwein.EndpointFiniteLocalArc
