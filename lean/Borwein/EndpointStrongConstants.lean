import Borwein.EndpointCombinedPhase

set_option autoImplicit false

namespace Borwein.EndpointStrongConstants
noncomputable section
open Complex FivePoleCircle EndpointRootCancellation

def sigma (a : Fin 3) : ℝ := ![(5+Real.sqrt 5)/2, -Real.sqrt 5, -(5-Real.sqrt 5)/2] a

theorem zeta_real : zeta.re=(Real.sqrt 5-1)/4 := by
  have hd := Real.cos_two_mul (Real.pi/5)
  rw [Real.cos_pi_div_five] at hd
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hz : zeta.re=Real.cos (2*Real.pi/5) := by
    simp only [zeta, AngularKernel.circle, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [hz]
  rw [show 2*(Real.pi/5)=2*Real.pi/5 by ring] at hd
  nlinarith

theorem first_pair : zeta+zeta^4=((Real.sqrt 5:ℂ)-1)/2 := by
  have hn := FiveRootProductExpansion.root_norm zeta zeta_primitive.pow_eq_one
  rw [← zeta_inv, Complex.inv_eq_conj hn, Complex.add_conj, zeta_real]
  push_cast
  ring

theorem second_pair : zeta^2+zeta^3=-(1+(Real.sqrt 5:ℂ))/2 := by
  have hc := cyclotomic zeta zeta_primitive
  have hp := first_pair
  linear_combination hc-hp

theorem constant_sigma (a : Fin 3) : constant a.val=(sigma a:ℂ) := by
  have h1 := first_pair
  have h2 := second_pair
  fin_cases a
  · have hc := constant_table (0:Fin 5)
    change constant 0=(((5+Real.sqrt 5)/2:ℝ):ℂ)
    push_cast
    change constant 0=2-zeta^2-zeta^3 at hc
    linear_combination hc-h2
  · have hc := constant_table (1:Fin 5)
    change constant 1=((-Real.sqrt 5:ℝ):ℂ)
    push_cast
    change constant 1=-zeta-zeta^4+zeta^2+zeta^3 at hc
    linear_combination hc-h1+h2
  · have hc := constant_table (2:Fin 5)
    change constant 2=((-(5-Real.sqrt 5)/2:ℝ):ℂ)
    push_cast
    change constant 2=zeta+zeta^4-2 at hc
    linear_combination hc+h1

theorem sigma_norm_lower (a : Fin 3) : 1 ≤ |sigma a| := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)
  have hp := Real.sqrt_nonneg (5:ℝ)
  have h2 : 2 ≤ Real.sqrt 5 := by nlinarith
  have h3 : Real.sqrt 5 ≤ 3 := by nlinarith
  fin_cases a
  · change 1 ≤ |(5+Real.sqrt 5)/2|
    exact (by linarith : (1:ℝ) ≤ (5+Real.sqrt 5)/2).trans (le_abs_self _)
  · change 1 ≤ |-Real.sqrt 5|
    rw [abs_neg, abs_of_nonneg hp]
    linarith
  · change 1 ≤ |-(5-Real.sqrt 5)/2|
    rw [neg_div, abs_neg, abs_of_nonneg (by linarith : 0 ≤ (5-Real.sqrt 5)/2)]
    linarith

theorem constant_norm_lower (a : Fin 3) : 1 ≤ ‖constant a.val‖ := by
  rw [constant_sigma, Complex.norm_real, Real.norm_eq_abs]
  exact sigma_norm_lower a

theorem constant_ne_zero (a : Fin 3) : constant a.val ≠ 0 := by
  have h := constant_norm_lower a
  exact norm_ne_zero_iff.mp (by linarith)

end
end Borwein.EndpointStrongConstants
