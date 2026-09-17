import Borwein.LargeBoxMainIntegral

namespace Borwein.LargeBoxAmplitude
noncomputable section
open Complex Set MeasureTheory LogFactorDerivatives FiveRootProductExpansion MainTermIdentification

theorem root_distance (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) : 1 ≤ ‖1-ξ‖ := by
  have hr := FifthRootCoordinates.real_upper ξ hξ hne
  have hc := FifthRootCoordinates.coordinate_square ξ hξ
  have hn := Complex.sq_norm (1-ξ)
  simp [Complex.normSq_apply] at hn
  nlinarith [norm_nonneg (1-ξ)]

theorem coefficient_distance (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (j : Fin 4) :
    1 ≤ ‖1-coefficients ξ j‖ := by
  apply root_distance
  · unfold coefficients
    rw [← pow_mul,mul_comm (j.val+1) 5,pow_mul,hξ.pow_eq_one,one_pow]
  · exact hξ.pow_ne_one_of_pos_of_lt (by omega) (by have hj := j.isLt; omega)

theorem kernel_upper (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hz : 0 ≤ z.re)
    (j : Fin 4) (x : ℝ) (hx : 0 ≤ x) : ‖kernel (coefficients ξ j) z x‖ ≤ 2 := by
  have hw := w_norm_le_one _ z x (coefficients_norm ξ (root_norm ξ hξ.pow_eq_one).le j) hz hx
  have hb := norm_sub_le (1:ℂ) (w (coefficients ξ j) z x)
  unfold kernel
  norm_num at hb
  linarith

theorem log_difference_bounds (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 6/5) (j : Fin 4) :
    -Real.log 40 ≤ Real.log ‖kernel (coefficients ξ j) z 1‖-Real.log ‖kernel (coefficients ξ j) z 0‖ ∧
    Real.log ‖kernel (coefficients ξ j) z 1‖-Real.log ‖kernel (coefficients ξ j) z 0‖ ≤ Real.log 2 := by
  have h10 := LargeBoxSeparation.coefficient_gap ξ z hξ hi j 1 (by norm_num)
  have h11 := kernel_upper ξ z hξ hz j 1 (by norm_num)
  have h00 : 1 ≤ ‖kernel (coefficients ξ j) z 0‖ := by simpa [kernel,w] using coefficient_distance ξ hξ j
  have h01 := kernel_upper ξ z hξ hz j 0 (by norm_num)
  have h1lo := Real.log_le_log (by norm_num : (0:ℝ) < 1/20) h10
  have h1hi := Real.log_le_log ((by norm_num : (0:ℝ) < 1/20).trans_le h10) h11
  have h0lo := Real.log_nonneg h00
  have h0hi := Real.log_le_log ((by norm_num : (0:ℝ) < 1).trans_le h00) h01
  have he : Real.log (1/20:ℝ)-Real.log 2 = -Real.log 40 := by
    rw [← Real.log_div (by norm_num : (1/20:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      show (1/20:ℝ)/2 = (40:ℝ)⁻¹ by norm_num,Real.log_inv]
  constructor <;> linarith

theorem lambda_real_upper (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 6/5) : (lambda ξ z).re ≤ (2/5:ℝ)*Real.log 80 := by
  have h0 := log_difference_bounds ξ z hξ hz hi 0
  have h1 := log_difference_bounds ξ z hξ hz hi 1
  have h2 := log_difference_bounds ξ z hξ hz hi 2
  have h3 := log_difference_bounds ξ z hξ hz hi 3
  have he : Real.log 40+Real.log 2 = Real.log 80 := by
    rw [← Real.log_mul (by norm_num : (40:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  rw [lambda_eq_endpoints]
  norm_num [Fin.sum_univ_four,shift,PeanoQuadrature.B1,Complex.add_re,Complex.sub_re,Complex.smul_re,f0,Complex.log_re]
  linarith [h0.1,h1.1,h2.2,h3.2]

theorem amplitude_norm_lt_six (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 6/5) : ‖amplitude ξ z‖ < 6 := by
  have hb := lambda_real_upper ξ z hξ hz hi
  have hl : Real.log ((80:ℝ)^2) < Real.log ((6:ℝ)^5) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow,Real.log_pow] at hl
  have he : (lambda ξ z).re < Real.log 6 := by norm_num at hl; linarith
  rw [amplitude,Complex.norm_exp]
  calc
    _ < Real.exp (Real.log 6) := Real.exp_lt_exp.mpr he
    _ = _ := Real.exp_log (by norm_num)

end
end Borwein.LargeBoxAmplitude
