import Borwein.EndpointRootLinear
import Borwein.EndpointRootPhaseSeries

set_option autoImplicit false

namespace Borwein.EndpointCombinedPhase
noncomputable section
open Complex FivePoleCircle EndpointRootCancellation EndpointRootLinear EndpointRootPhaseSeries EndpointTailMain

def combined (a : ℕ) (x : ℂ) : ℂ := ∑ j : Fin 4, weight a j*exp (phase (zeta^(j.val+1)) x)

theorem first_coefficient (j : Fin 4) : coefficient (zeta^(j.val+1)) 1 =
    zeta^(j.val+1)/(1-zeta^(j.val+1))+1/2 := by norm_num [coefficient]

theorem phase_zero (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) : phase ξ 0=0 := by
  have h := phase_bound ξ 0 hξ (by norm_num)
  simpa using h

theorem combined_zero (a : ℕ) : combined a 0=constant a := by
  unfold combined constant
  apply Finset.sum_congr rfl
  intro j _
  rw [phase_zero _ (actual_root_primitive j), exp_zero, mul_one]

theorem combined_remainder (a : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1/10) :
    ‖combined a x-constant a-linear a*x‖ ≤ 8*‖x‖^2 := by
  have he : combined a x-constant a-linear a*x =
      ∑ j : Fin 4, weight a j*(exp (phase (zeta^(j.val+1)) x)-1-coefficient (zeta^(j.val+1)) 1*x) := by
    simp only [combined, constant, linear, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [first_coefficient]
    ring
  rw [he]
  apply (norm_sum_le _ _).trans
  have hb : ∑ j : Fin 4, ‖weight a j*(exp (phase (zeta^(j.val+1)) x)-1-coefficient (zeta^(j.val+1)) 1*x)‖ ≤
      ∑ _j : Fin 4, 2*‖x‖^2 := by
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul, weight_norm, one_mul]
    exact exponential_linear_remainder _ x (actual_root_primitive j) hx
  exact hb.trans_eq (by simp; ring)

/-- The weak modes retain the first nonzero term, with the manuscript's quadratic bound. -/
theorem weak_combined_remainder (a : ℕ) (ha : a=3 ∨ a=4) (x : ℂ) (hx : ‖x‖ ≤ 1/10) :
    ‖combined a x+x‖ ≤ 8*‖x‖^2 := by
  have h := combined_remainder a x hx
  rw [weak_constant a ha, weak_linear a ha] at h
  simpa using h

theorem weak_combined_zero (a : ℕ) (ha : a=3 ∨ a=4) : combined a 0=0 := by
  rw [combined_zero, weak_constant a ha]

end
end Borwein.EndpointCombinedPhase
