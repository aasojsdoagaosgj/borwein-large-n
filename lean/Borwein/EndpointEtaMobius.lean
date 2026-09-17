import Borwein.EndpointEta

set_option autoImplicit false

namespace Borwein.EndpointEtaMobius
noncomputable section
open Complex EndpointEta
open scoped Real

theorem sqrt_mul_args (x y : ℂ) (hx : x ≠ 0) (hy : y ≠ 0)
    (ha : -Real.pi < arg x+arg y ∧ arg x+arg y ≤ Real.pi) :
    sqrt (x*y) = sqrt x*sqrt y := by
  rw [sqrt_eq_exp (mul_ne_zero hx hy), Complex.log_mul hx hy ha,
    add_div, Complex.exp_add, ← sqrt_eq_exp hx, ← sqrt_eq_exp hy]

theorem sqrt_mul_right (x y : ℂ) (hx : 0 < x.re) (hy : 0 < y.re) :
    sqrt (x*y) = sqrt x*sqrt y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have hax := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hay := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  apply sqrt_mul_args x y hx0 hy0
  constructor <;> linarith

theorem sqrt_I_mul_right (x : ℂ) (hx : 0 < x.re) :
    sqrt (I*x) = sqrt I*sqrt x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hax := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  apply sqrt_mul_args I x I_ne_zero hx0
  rw [Complex.arg_I]
  constructor <;> linarith [Real.pi_pos]

def J (z : ℂ) : ℂ := sqrt (-I*z)

theorem sqrt_upper (z : ℂ) (hz : 0 < z.im) : sqrt z = sqrt I*J z := by
  have hr : 0 < (-I*z).re := by simpa using hz
  have he : I*(-I*z) = z := by simp [← mul_assoc]
  simpa only [he, J] using sqrt_I_mul_right (-I*z) hr

theorem eta_S (z : ℂ) (hz : 0 < z.im) :
    ModularForm.eta (-1/z) = J z*ModularForm.eta z := by
  rw [eta_inversion z hz, sqrt_upper z hz]
  have hI : sqrt I ≠ 0 := by rw [sqrt_eq_exp I_ne_zero]; exact Complex.exp_ne_zero _
  simp [mul_assoc, hI]

theorem eta_sub_nat (z : ℂ) (k : ℕ) :
    ModularForm.eta (z-k) = exp (-(Real.pi:ℂ)*I*k/12)*ModularForm.eta z := by
  have he := eta_add_nat (z-k) k
  rw [sub_add_cancel] at he
  rw [he, ← mul_assoc, ← Complex.exp_add]
  have hzero : -(Real.pi:ℂ)*I*k/12+(Real.pi:ℂ)*I*k/12 = 0 := by ring
  rw [hzero, Complex.exp_zero, one_mul]

theorem inverse_upper (z : ℂ) (hz : 0 < z.im) : 0 < (-1/z).im := by
  simpa using UpperHalfPlane.im_pnat_div_pos 1 (⟨z,hz⟩ : UpperHalfPlane)

/-- Lower unipotent transformation, with its actual eta multiplier, for every natural k. -/
theorem eta_lower (z : ℂ) (k : ℕ) (hz : 0 < z.im) :
    ModularForm.eta (z/(k*z+1)) =
      exp (-(Real.pi:ℂ)*I*k/12)*sqrt (k*z+1)*ModularForm.eta z := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let u : ℂ := -1/z-k
  have hu : 0 < u.im := by simpa [u] using inverse_upper z hz
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hd : (k:ℂ)*z+1 ≠ 0 := by
    have he : (k:ℂ)*z+1 = -z*u := by dsimp [u]; field_simp; ring
    rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr hz0) hu0
  have harg : -1/u = z/(k*z+1) := by
    have he : u = -(k*z+1)/z := by dsimp [u]; field_simp; ring
    rw [he]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_neg, inv_inv]
    ring
  have hj : J u*J z = sqrt (k*z+1) := by
    have hru : 0 < (-I*u).re := by simpa using hu
    have hrz : 0 < (-I*z).re := by simpa using hz
    rw [J, J, ← sqrt_mul_right _ _ hru hrz]
    congr 1
    dsimp [u]
    field_simp
    ring_nf
    simp [I_sq]
  rw [← harg, eta_S u hu]
  dsimp only [u]
  rw [eta_sub_nat, eta_S z hz]
  calc
    _ = exp (-(Real.pi:ℂ)*I*k/12)*(J u*J z)*ModularForm.eta z := by ring
    _ = _ := by rw [hj]

end
end Borwein.EndpointEtaMobius
