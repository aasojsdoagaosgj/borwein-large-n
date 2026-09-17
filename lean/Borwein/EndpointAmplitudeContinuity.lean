import Borwein.EndpointTailContinuity
import Borwein.EndpointStrongPolynomial
import Borwein.EndpointGaussianIntegral

set_option autoImplicit false

namespace Borwein.EndpointAmplitudeContinuity
noncomputable section
open Complex EndpointPhaseAtoms EndpointActualPhase EndpointTailContinuity

def strongError (a : Fin 3) (n : ℕ) (v y : ℝ) : ℂ :=
  EndpointStrongPolynomial.mainTail a.val n (coordinate v y)/
    EndpointStrongPolynomial.leading a n (coordinate v y)-1

def weakError (a n : ℕ) (v y : ℝ) : ℂ :=
  EndpointWeakTail.filteredMain a n (coordinate v y)/
    EndpointWeakTail.weakLeading n (coordinate v y)-1

theorem coordinate_continuous (v : ℝ) : Continuous (coordinate v) := by
  unfold coordinate
  fun_prop

theorem main_continuous (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointRootAsymptotic.main (coordinate v y)) := by
  unfold EndpointRootAsymptotic.main
  apply Continuous.cexp
  exact (continuous_const.div (coordinate_continuous v) (fun y => coordinate_ne_zero v y hv)).sub
    ((coordinate_continuous v).div_const _)

theorem common_leading_continuous (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Continuous (fun y => exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*coordinate v y)-coordinate v y/6)) := by
  have hf : Continuous (f0 n v) := continuous_iff_continuousAt.mpr (fun y => (f0_deriv n v y hn hv).continuousAt)
  have hh := (hf.sub ((coordinate_continuous v).div_const 6)).cexp
  exact hh.congr (fun y => by simp only [Pi.sub_apply, f0_eq_actual n v y hn hv])

theorem mainTail_continuous (a n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointStrongPolynomial.mainTail a n (coordinate v y)) := by
  apply (main_continuous v hv).mul
  apply continuous_finsetSum
  intro j _
  exact (root_tail_continuous n j v hv).const_mul _

theorem filteredMain_continuous (a n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointWeakTail.filteredMain a n (coordinate v y)) := by
  apply (main_continuous v hv).mul
  apply continuous_finsetSum
  intro j _
  exact ((root_tail_continuous n j v hv).sub continuous_const).const_mul _

theorem strongError_continuous (a : Fin 3) (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Continuous (strongError a n v) := by
  apply Continuous.sub _ continuous_const
  exact (mainTail_continuous a.val n v hv).div
    ((common_leading_continuous n v hn hv).const_mul _)
    (fun y => EndpointStrongPolynomial.leading_ne_zero a n (coordinate v y))

theorem weakError_continuous (a n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Continuous (weakError a n v) := by
  apply Continuous.sub _ continuous_const
  apply (filteredMain_continuous a n v hv).div _
    (fun y => EndpointWeakTail.weakLeading_ne_zero n (coordinate v y))
  apply Continuous.mul _ (common_leading_continuous n v hn hv)
  unfold EndpointSharpTail.x coordinate
  fun_prop

end
end Borwein.EndpointAmplitudeContinuity
