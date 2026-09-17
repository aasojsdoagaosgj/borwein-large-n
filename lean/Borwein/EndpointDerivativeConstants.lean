import Borwein.EndpointProfileBudget
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace Borwein.EndpointDerivativeConstants
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseDerivatives EndpointActualPhase EndpointProfileBudget

theorem exponential_lower : (24469/100:ℝ) ≤ Real.exp (11/2) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 11/2) 20
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith

theorem reciprocal_upper : 0 ≤ 1/(Real.exp (11/2)-1) ∧
    1/(Real.exp (11/2)-1) ≤ (100/24369:ℝ) := by
  have hp : 0 < Real.exp (11/2)-1 := by linarith [exponential_lower]
  constructor
  · positivity
  · apply (div_le_iff₀ hp).mpr
    linarith [exponential_lower]

theorem B2_identity : B2 (11/2)=(173/5:ℝ)/(Real.exp (11/2)-1) := by
  have hp : Real.exp (11/2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have he : Real.exp (11/2)-1 ≠ 0 := by linarith [exponential_lower]
  unfold B2 quadratic
  rw [Real.exp_neg]
  norm_num
  field_simp

theorem B3_identity : B3 (11/2)=(2369/10:ℝ)*(1/(Real.exp (11/2)-1))+
    (1331/10:ℝ)*(1/(Real.exp (11/2)-1))^2 := by
  have hp : Real.exp (11/2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have he : Real.exp (11/2)-1 ≠ 0 := by linarith [exponential_lower]
  unfold B3 quadratic
  rw [Real.exp_neg]
  norm_num
  field_simp
  ring

theorem B2_bound : B2 (11/2) ≤ (71/500:ℝ) := by
  rw [B2_identity, div_eq_mul_one_div]
  have hh := mul_le_mul_of_nonneg_left reciprocal_upper.2 (by norm_num : (0:ℝ) ≤ 173/5)
  linarith

theorem B3_bound : B3 (11/2) ≤ (49/50:ℝ) := by
  rw [B3_identity]
  have hh := reciprocal_upper
  have hs : (1/(Real.exp (11/2)-1))^2 ≤ (100/24369:ℝ)^2 := by nlinarith
  nlinarith

theorem second_correction_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : v^3*‖q2 n v y‖ ≤ (71/500:ℝ) :=
  (uniform_second_bound n v y (11/2) hn hv (by norm_num) hτ).trans B2_bound

theorem third_correction_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : v^4*‖q3 n v y‖ ≤ (49/50:ℝ) :=
  (uniform_third_bound n v y (11/2) hn hv (by norm_num) hτ).trans B3_bound

theorem A_bounds : (263/1000:ℝ) ≤ A ∧ A ≤ (2633/10000:ℝ) := by
  unfold A
  constructor <;> nlinarith [Real.pi_gt_d4, Real.pi_lt_d4, Real.pi_pos]

theorem second_main_real (n : ℕ) (v : ℝ) :
    (f2 n v 0).re=2*A/v^3+(q2 n v 0).re := by
  simp only [f2, atom, Complex.ofReal_zero, coordinate, zero_mul, add_zero,
    neg_zero, Complex.exp_zero, show (2:ℕ)+1=3 by decide]
  rw [← mul_div_assoc, mul_one]
  have he : (2*(A:ℂ)/(v:ℂ)^3)=((2*A/v^3:ℝ):ℂ) := by push_cast; rfl
  rw [he, Complex.add_re, Complex.ofReal_re]

theorem second_main_bounds (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    (38/100:ℝ) ≤ v^3*(f2 n v 0).re ∧ v^3*(f2 n v 0).re ≤ (67/100:ℝ) := by
  have hb := second_correction_bound n v 0 hn hv hτ
  have hu := mul_le_mul_of_nonneg_left (Complex.re_le_norm (q2 n v 0)) (by positivity : 0 ≤ v^3)
  have hln : -‖q2 n v 0‖ ≤ (q2 n v 0).re := by
    have hh := Complex.re_le_norm (-q2 n v 0)
    simp only [Complex.neg_re, norm_neg] at hh
    linarith
  have hl := mul_le_mul_of_nonneg_left hln (by positivity : 0 ≤ v^3)
  have he : v^3*(2*A/v^3+(q2 n v 0).re)=2*A+v^3*(q2 n v 0).re := by field_simp
  rw [second_main_real, he]
  constructor <;> nlinarith [A_bounds.1, A_bounds.2]

theorem third_main_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : v^4*‖f3 n v y‖ ≤ (64/25:ℝ) := by
  have hA : 0 ≤ A := by linarith [A_bounds.1]
  have ha := atom_bound 0 3 v y hv
  norm_num at ha
  have hh := norm_add_le (-6*(A:ℂ)*atom 0 3 v y) (q3 n v y)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA] at hh
  norm_num at hh
  have ht := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 6*A)
  have hb := mul_le_mul_of_nonneg_left (hh.trans (add_le_add ht le_rfl)) (by positivity : 0 ≤ v^4)
  have he : v^4*(6*A*(1/v^4)+‖q3 n v y‖)=6*A+v^4*‖q3 n v y‖ := by field_simp
  simp only [one_div] at he
  rw [he] at hb
  have hfin := hb.trans (show 6*A+v^4*‖q3 n v y‖ ≤ (64/25:ℝ) from by
    nlinarith [third_correction_bound n v y hn hv hτ, A_bounds.2])
  simpa only [f3, neg_mul] using hfin

end
end Borwein.EndpointDerivativeConstants
