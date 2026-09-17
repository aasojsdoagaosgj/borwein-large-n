import Borwein.EndpointPositiveFinite

set_option autoImplicit false

namespace Borwein.EndpointPositiveContinuity
noncomputable section
open Complex EndpointPositiveKernel EndpointPositiveFinite

theorem point_continuous (v : ℝ) : Continuous (point v) := by
  unfold point EndpointPhaseAtoms.coordinate
  fun_prop

theorem tail_continuous (n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointFiniteConnection.tail n (point v y)) := by
  apply EndpointTailContinuity.tail_continuous n (point v) (Real.exp (-v)) (point_continuous v)
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  intro y
  exact (point_norm v y).le

theorem tail_ne_zero (n : ℕ) (v y : ℝ) (hv : 0 < v) :
    EndpointFiniteConnection.tail n (point v y) ≠ 0 := by
  rw [← EndpointTailLog.exp_tailLog n (point v y) (point_norm_lt_one v y hv)]
  exact exp_ne_zero _

theorem G_identity (v y : ℝ) (hv : 0 < v) :
    EndpointEta.G (point v y)=1/EndpointFiniteConnection.tail 0 (point v y) := by
  apply (eq_div_iff (tail_ne_zero 0 v y hv)).mpr
  have hh := EndpointFiniteConnection.polynomial_eq_G_tail 0 (point v y) (point_norm_lt_one v y hv)
  simpa [Borwein.polynomial] using hh.symm

theorem G_continuous (v : ℝ) (hv : 0 < v) : Continuous (fun y => EndpointEta.G (point v y)) := by
  have hh : Continuous (fun y => 1/EndpointFiniteConnection.tail 0 (point v y)) :=
    continuous_const.div (tail_continuous 0 v hv) (fun y => tail_ne_zero 0 v y hv)
  exact hh.congr (fun y => (G_identity v y hv).symm)

theorem value_continuous (n : ℕ) (v : ℝ) : Continuous (value n v) :=
  ((Borwein.polynomial n).continuous_eval₂ (Int.castRingHom ℂ)).comp (point_continuous v)

theorem difference_continuous (n : ℕ) (v : ℝ) (hv : 0 < v) : Continuous (difference n v) :=
  (value_continuous n v).sub (G_continuous v hv)

end
end Borwein.EndpointPositiveContinuity
