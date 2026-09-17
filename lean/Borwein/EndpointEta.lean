import Mathlib.NumberTheory.ModularForms.Discriminant

set_option autoImplicit false

namespace Borwein.EndpointEta
noncomputable section
open Complex
open scoped Real

/-- The analytic Euler product; formal power series are kept separate. -/
def euler (q : ℂ) : ℂ := ∏' j : ℕ, (1 - q ^ (j + 1))

/-- The infinite product used in the endpoint argument, manuscript (2.1). -/
def G (q : ℂ) : ℂ := euler q / euler (q ^ 5)

def q (z : ℂ) : ℂ := exp (2 * Real.pi * I * z)

theorem eta_product (z : ℂ) :
    ModularForm.eta z = exp (Real.pi * I * z / 12) * euler (q z) := by
  unfold ModularForm.eta euler q
  simp only [ModularForm.eta_q_eq_pow, Function.Periodic.qParam]
  congr 2
  push_cast
  ring

theorem q_five (z : ℂ) : q (5*z) = q z ^ 5 := by
  unfold q
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem euler_q_ne_zero (z : ℂ) (hz : 0 < z.im) : euler (q z) ≠ 0 := by
  simpa only [euler, q, ModularForm.eta_q_eq_pow] using ModularForm.eta_tprod_ne_zero hz

theorem G_eta (z : ℂ) :
    G (q z) = exp (Real.pi * I * z / 3) * (ModularForm.eta z / ModularForm.eta (5*z)) := by
  rw [eta_product, eta_product, q_five]
  unfold G
  rw [mul_div_mul_comm, ← mul_assoc, ← Complex.exp_sub, ← Complex.exp_add]
  have he : (Real.pi:ℂ)*I*z/3+((Real.pi:ℂ)*I*z/12-(Real.pi:ℂ)*I*(5*z)/12) = 0 := by ring
  rw [he, Complex.exp_zero, one_mul]

theorem q_add_one (z : ℂ) : q (z+1) = q z := by
  unfold q
  rw [mul_add, mul_one]
  exact Complex.exp_periodic _

/-- The phase-sensitive T transformation, derived from the product definition. -/
theorem eta_add_one (z : ℂ) :
    ModularForm.eta (z+1) = exp (Real.pi * I / 12) * ModularForm.eta z := by
  rw [eta_product, eta_product, q_add_one, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem eta_add_nat (z : ℂ) (k : ℕ) :
    ModularForm.eta (z+k) = exp (Real.pi * I * k / 12) * ModularForm.eta z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, eta_add_one, ih, ← mul_assoc,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring

/-- The S transformation retains the principal square roots and their phase. -/
theorem eta_inversion (z : ℂ) (hz : 0 < z.im) :
    ModularForm.eta (-1/z) = (sqrt I)⁻¹ * (sqrt z * ModularForm.eta z) := by
  exact ModularForm.eta_comp_eq_csqrt_I_inv hz

theorem euler_inversion (z : ℂ) (hz : 0 < z.im) :
    euler (q (-1/z)) = (sqrt I)⁻¹ * sqrt z *
      exp (Real.pi * I * (z+1/z) / 12) * euler (q z) := by
  have he := eta_inversion z hz
  rw [eta_product, eta_product] at he
  have hex : exp ((Real.pi:ℂ)*I*(-1/z)/12) ≠ 0 := Complex.exp_ne_zero _
  apply (mul_left_cancel₀ hex)
  rw [he]
  have hsum : (Real.pi:ℂ)*I*(-1/z)/12 + (Real.pi:ℂ)*I*(z+1/z)/12 =
      (Real.pi:ℂ)*I*z/12 := by ring
  calc
    _ = (sqrt I)⁻¹ * sqrt z * exp ((Real.pi:ℂ)*I*z/12) * euler (q z) := by ring
    _ = exp ((Real.pi:ℂ)*I*(-1/z)/12) *
        ((sqrt I)⁻¹ * sqrt z * exp ((Real.pi:ℂ)*I*(z+1/z)/12) * euler (q z)) := by
      rw [← hsum, Complex.exp_add]
      ring

end
end Borwein.EndpointEta
