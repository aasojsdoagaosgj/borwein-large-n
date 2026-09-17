import Borwein.EndpointRootCancellation

set_option autoImplicit false

namespace Borwein.EndpointRootLinear
noncomputable section
open Complex FivePoleCircle EndpointRootAsymptotic EndpointRootCancellation

theorem linear_kernel (j : Fin 4) :
    zeta^(j.val+1)/(1-zeta^(j.val+1))+1/2 =
      zeta^(j.val+1)*(4+3*zeta^(j.val+1)+2*zeta^(2*(j.val+1))+zeta^(3*(j.val+1)))/5+1/2 := by
  have he : zeta^(j.val+1)/(1-zeta^(j.val+1)) = zeta^(j.val+1)*(1/(1-zeta^(j.val+1))) := by ring
  rw [he, root_inverse_polynomial]
  ring

theorem weak_linear (a : ℕ) (ha : a=3 ∨ a=4) : linear a = -1 := by
  have h5 := zeta_primitive.pow_eq_one
  have hc := cyclotomic zeta zeta_primitive
  rcases ha with rfl|rfl <;>
    norm_num [linear, Fin.sum_univ_succ, weight_polynomial, linear_kernel] <;>
    ring_nf <;>
    simp only [pow_eq_pow_mod 5 h5, pow_eq_pow_mod 6 h5, pow_eq_pow_mod 7 h5,
      pow_eq_pow_mod 8 h5, pow_eq_pow_mod 9 h5, pow_eq_pow_mod 10 h5,
      pow_eq_pow_mod 11 h5, pow_eq_pow_mod 12 h5, pow_eq_pow_mod 13 h5,
      pow_eq_pow_mod 14 h5, pow_eq_pow_mod 15 h5, pow_eq_pow_mod 16 h5,
      pow_eq_pow_mod 17 h5, pow_eq_pow_mod 18 h5, pow_eq_pow_mod 19 h5,
      pow_eq_pow_mod 20 h5, pow_eq_pow_mod 21 h5, pow_eq_pow_mod 22 h5,
      pow_eq_pow_mod 23 h5] <;>
    norm_num <;> linear_combination (1/5:ℂ)*hc

theorem kappa_norm (j : Fin 4) : ‖kappa j‖=1 := by
  have hz := FiveRootProductExpansion.root_norm zeta zeta_primitive.pow_eq_one
  rw [kappa_polynomial]
  fin_cases j <;> norm_num [norm_pow, hz]

theorem weight_norm (a : ℕ) (j : Fin 4) : ‖weight a j‖=1 := by
  have hz := FiveRootProductExpansion.root_norm zeta zeta_primitive.pow_eq_one
  simp only [weight, norm_mul, norm_zpow, hz, one_zpow, one_mul, kappa_norm]

end
end Borwein.EndpointRootLinear
