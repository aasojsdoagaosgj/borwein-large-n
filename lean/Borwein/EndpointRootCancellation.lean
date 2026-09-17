import Borwein.EndpointNormalizedTail

set_option autoImplicit false

namespace Borwein.EndpointRootCancellation
noncomputable section
open Complex FivePoleCircle EndpointRootAsymptotic

def weight (a : ℕ) (j : Fin 4) : ℂ := zeta^(-((a*(j.val+1):ℕ):ℤ))*kappa j
def constant (a : ℕ) : ℂ := ∑ j : Fin 4, weight a j
def linear (a : ℕ) : ℂ := ∑ j : Fin 4, weight a j*(zeta^(j.val+1)/(1-zeta^(j.val+1))+1/2)

theorem zeta_exp : zeta = exp (2*(Real.pi:ℂ)*I/5) := by
  rw [zeta, AngularKernel.circle_eq_exp]
  congr 1
  push_cast
  ring

theorem kappa_polynomial (j : Fin 4) : kappa j = ![-zeta^2,1,1,-zeta^3] j := by
  have h1 : exp (-(Real.pi:ℂ)*I/5)*(-1) = zeta^2 := by
    rw [zeta_exp, ← exp_nat_mul, ← exp_pi_mul_I, ← exp_add]
    congr 1
    ring
  have h4 : exp ((Real.pi:ℂ)*I/5)*(-1) = zeta^3 := by
    rw [zeta_exp, ← exp_nat_mul, ← exp_pi_mul_I, ← exp_add]
    congr 1
    ring
  fin_cases j
  · change exp (-(Real.pi:ℂ)*I/5) = -zeta^2
    linear_combination -h1
  · rfl
  · rfl
  · change exp ((Real.pi:ℂ)*I/5) = -zeta^3
    linear_combination -h4

theorem zeta_inv : zeta⁻¹=zeta^4 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using zeta_primitive.pow_eq_one

theorem negative_power (k : ℕ) : zeta^(-(k:ℤ))=zeta^((4*k)%5) := by
  rw [zpow_neg, zpow_natCast, ← inv_pow, zeta_inv, ← pow_mul]
  exact pow_eq_pow_mod _ zeta_primitive.pow_eq_one

theorem weight_polynomial (a : ℕ) (j : Fin 4) : weight a j =
    zeta^((4*(a*(j.val+1)))%5)*(![-zeta^2,1,1,-zeta^3] j) := by
  rw [weight, negative_power, kappa_polynomial]

theorem constant_table (a : Fin 5) : constant a.val =
    ![2-zeta^2-zeta^3, -zeta-zeta^4+zeta^2+zeta^3, zeta+zeta^4-2, 0, 0] a := by
  have h5 := zeta_primitive.pow_eq_one
  fin_cases a <;>
    norm_num [constant, Fin.sum_univ_succ, weight_polynomial] <;>
    ring_nf <;>
    (try simp only [pow_eq_pow_mod 5 h5, pow_eq_pow_mod 6 h5, pow_eq_pow_mod 7 h5]) <;>
    norm_num <;> ring

theorem weak_constant (a : ℕ) (ha : a=3 ∨ a=4) : constant a=0 := by
  rcases ha with rfl|rfl
  · exact constant_table (3:Fin 5)
  · exact constant_table (4:Fin 5)

theorem cyclotomic (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) : ξ^4+ξ^3+ξ^2+ξ+1=0 := by
  have h := hξ.geom_sum_eq_zero (by norm_num : 1<5)
  norm_num [Finset.sum_range_succ] at h
  linear_combination h

theorem inverse_polynomial (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) :
    1/(1-ξ)=(4+3*ξ+2*ξ^2+ξ^3)/5 := by
  have hn : ξ ≠ 1 := hξ.ne_one (by norm_num)
  have hd : 1-ξ ≠ 0 := sub_ne_zero.mpr hn.symm
  have hc := cyclotomic ξ hξ
  field_simp
  linear_combination hc

theorem root_inverse_polynomial (j : Fin 4) :
    1/(1-zeta^(j.val+1))=(4+3*zeta^(j.val+1)+2*zeta^(2*(j.val+1))+zeta^(3*(j.val+1)))/5 := by
  have h := inverse_polynomial _ (EndpointTailMain.actual_root_primitive j)
  simpa only [← pow_mul, Nat.mul_comm (j.val+1)] using h

end
end Borwein.EndpointRootCancellation
