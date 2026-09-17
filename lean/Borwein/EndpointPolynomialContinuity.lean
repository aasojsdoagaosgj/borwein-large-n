import Borwein.EndpointAmplitudeContinuity
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

namespace Borwein.EndpointPolynomialContinuity
noncomputable section
open Complex EndpointPhaseAtoms EndpointTailContinuity EndpointAmplitudeContinuity

theorem root_tail_ne_zero (n : ℕ) (j : Fin 4) (v y : ℝ) (hv : 0 < v) :
    EndpointFiniteConnection.tail n (root j v y) ≠ 0 := by
  have hq : ‖root j v y‖ < 1 := EndpointFiniteConnection.root_norm j _ (by simpa [coordinate] using hv)
  rw [← EndpointTailLog.exp_tailLog n (root j v y) hq]
  exact exp_ne_zero _

theorem root_G_identity (j : Fin 4) (v y : ℝ) (hv : 0 < v) :
    EndpointEta.G (root j v y)=1/EndpointFiniteConnection.tail 0 (root j v y) := by
  apply (eq_div_iff (root_tail_ne_zero 0 j v y hv)).mpr
  have hh := EndpointFiniteConnection.polynomial_eq_G_tail 0 (root j v y)
    (EndpointFiniteConnection.root_norm j _ (by simpa [coordinate] using hv))
  simpa [Borwein.polynomial] using hh.symm

theorem root_G_continuous (j : Fin 4) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointEta.G (root j v y)) := by
  have hh : Continuous (fun y => 1/EndpointFiniteConnection.tail 0 (root j v y)) :=
    continuous_const.div (root_tail_continuous 0 j v hv) (fun y => root_tail_ne_zero 0 j v y hv)
  exact hh.congr (fun y => (root_G_identity j v y hv).symm)

theorem root_polynomial_continuous (n : ℕ) (j : Fin 4) (v : ℝ) :
    Continuous (fun y => Polynomial.eval₂ (Int.castRingHom ℂ) (root j v y) (Borwein.polynomial n)) :=
  ((Borwein.polynomial n).continuous_eval₂ (Int.castRingHom ℂ)).comp (root_continuous j v)

theorem polynomialSum_continuous (a n : ℕ) (v : ℝ) :
    Continuous (fun y => EndpointStrongPolynomial.polynomialSum a n (coordinate v y)) := by
  apply continuous_finsetSum
  intro j _
  exact (root_polynomial_continuous n j v).const_mul _

theorem polynomialDifference_continuous (a n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointWeakPolynomial.polynomialDifference a n (coordinate v y)) := by
  apply continuous_finsetSum
  intro j _
  exact ((root_polynomial_continuous n j v).sub (root_G_continuous j v hv)).const_mul _

theorem strongEta_continuous (a n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointStrongPolynomial.strongEta a n (coordinate v y)) := by
  have hh := (polynomialSum_continuous a n v).sub (mainTail_continuous a n v hv)
  apply hh.congr
  intro y
  change EndpointStrongPolynomial.polynomialSum a n (coordinate v y)-EndpointStrongPolynomial.mainTail a n (coordinate v y)=_
  rw [EndpointStrongPolynomial.polynomial_decomposition a n _ (by simpa [coordinate] using hv)]
  ring

theorem etaRemainder_continuous (a n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointWeakPolynomial.etaRemainder a n (coordinate v y)) := by
  have hh := (polynomialDifference_continuous a n v hv).sub (filteredMain_continuous a n v hv)
  apply hh.congr
  intro y
  change EndpointWeakPolynomial.polynomialDifference a n (coordinate v y)-EndpointWeakTail.filteredMain a n (coordinate v y)=_
  rw [EndpointWeakPolynomial.polynomial_decomposition a n _ (by simpa [coordinate] using hv)]
  ring

end
end Borwein.EndpointPolynomialContinuity
