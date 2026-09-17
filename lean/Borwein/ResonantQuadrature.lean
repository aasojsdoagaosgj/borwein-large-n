import Borwein.ExponentialKernelRemainder
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Field.GeomSum

namespace Borwein.ResonantQuadrature
noncomputable section
open Complex MeasureTheory ExponentialKernelRemainder

def finiteSum (M : ℕ) (A : ℂ) : ℂ :=
  ∑ j ∈ Finset.range M, Complex.exp (-A*(((j+1:ℕ):ℂ)/(M:ℂ)))

theorem exponential_term (M j : ℕ) (A : ℂ) :
    Complex.exp (-A*(((j+1:ℕ):ℂ)/(M:ℂ))) = Complex.exp (-A/(M:ℂ))^(j+1) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

theorem exponential_power (M : ℕ) (A : ℂ) (hM : 0 < M) :
    Complex.exp (-A/(M:ℂ))^M = Complex.exp (-A) := by
  have hm : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [← Complex.exp_nat_mul]
  congr 1
  field_simp

theorem finite_sum_formula (M : ℕ) (A : ℂ) (hM : 0 < M) (hA0 : A ≠ 0)
    (hA : ‖A/(M:ℂ)‖ < 2*Real.pi) :
    finiteSum M A = (1-Complex.exp (-A))/(Complex.exp (A/(M:ℂ))-1) := by
  have hm : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have he := exp_ne_one (A/(M:ℂ)) (div_ne_zero hA0 hm) hA
  have hq : Complex.exp (-A/(M:ℂ)) ≠ 1 := by
    rw [neg_div,Complex.exp_neg]
    exact inv_ne_one.mpr he
  unfold finiteSum
  simp_rw [exponential_term,pow_succ]
  rw [← Finset.sum_mul,geom_sum_eq hq,exponential_power M A hM]
  simp only [neg_div,Complex.exp_neg]
  have he0 := Complex.exp_ne_zero (A/(M:ℂ))
  have hd : Complex.exp (A/(M:ℂ))-1 ≠ 0 := sub_ne_zero.mpr he
  have hi : (Complex.exp (A/(M:ℂ)))⁻¹-1 ≠ 0 := sub_ne_zero.mpr (inv_ne_one.mpr he)
  field_simp
  ring

theorem integral_formula (A : ℂ) (hA : A ≠ 0) :
    (∫ x in (0:ℝ)..1, Complex.exp (-A*(x:ℂ))) = (1-Complex.exp (-A))/A := by
  rw [integral_exp_mul_complex (neg_ne_zero.mpr hA)]
  simp
  ring

theorem error_identity (M : ℕ) (A : ℂ) (hM : 0 < M)
    (hA : ‖A/(M:ℂ)‖ < 2*Real.pi) :
    finiteSum M A-(M:ℂ)*(∫ x in (0:ℝ)..1, Complex.exp (-A*(x:ℂ))) =
      (1-Complex.exp (-A))*kernel (A/(M:ℂ)) := by
  by_cases hA0 : A = 0
  · subst A
    simp [finiteSum]
  rw [finite_sum_formula M A hM hA0 hA,integral_formula A hA0,kernel]
  simp only [one_div,inv_div]
  ring

theorem endpoint_bound (A : ℂ) (hA : 0 ≤ A.re) : ‖1-Complex.exp (-A)‖ ≤ 2 := by
  have ht := norm_sub_le (1:ℂ) (Complex.exp (-A))
  rw [norm_one,Complex.norm_exp,Complex.neg_re] at ht
  have he : Real.exp (-A.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem error_bound (M : ℕ) (A : ℂ) (hM : 0 < M) (hA0 : 0 ≤ A.re)
    (hA : ‖A/(M:ℂ)‖ < 2*Real.pi) :
    ‖finiteSum M A-(M:ℂ)*(∫ x in (0:ℝ)..1, Complex.exp (-A*(x:ℂ)))‖ ≤
      2*kappa ‖A/(M:ℂ)‖ := by
  rw [error_identity M A hM hA,norm_mul]
  exact mul_le_mul (endpoint_bound A hA0) (kernel_bound _ hA) (norm_nonneg _) (by norm_num)

end
end Borwein.ResonantQuadrature
