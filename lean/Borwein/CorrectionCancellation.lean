import Borwein.MainTermIdentification

namespace Borwein.CorrectionCancellation
noncomputable section
open scoped BigOperators
open Complex LogFactorDerivatives FiveRootProductExpansion FifthRootLogarithm MainTermIdentification

theorem coefficients_inverse (ξ : ℂ) (hξ : ξ^5 = 1) (j : Fin 4) :
    coefficients ξ j.rev*coefficients ξ j = 1 := by
  rw [conjugate_coefficient ξ hξ,mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq]
  have hn : ‖coefficients ξ j‖ = 1 := by simp [coefficients,norm_pow,root_norm ξ hξ]
  rw [hn]
  norm_num

theorem inverse_pair (u v : ℂ) (hu : u ≠ 1) (hv : v ≠ 1) (huv : u*v = 1) :
    u/(1-u)+v/(1-v) = -1 := by
  have hdu : 1-u ≠ 0 := sub_ne_zero.mpr hu.symm
  have hdv : 1-v ≠ 0 := sub_ne_zero.mpr hv.symm
  field_simp
  linear_combination -huv

theorem coefficient_pair (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (j : Fin 4) :
    coefficients ξ j/(1-coefficients ξ j)+
      coefficients ξ j.rev/(1-coefficients ξ j.rev) = -1 := by
  apply inverse_pair
  · exact hξ.pow_ne_one_of_pos_of_lt (by omega) (by have h := j.isLt; omega)
  · exact hξ.pow_ne_one_of_pos_of_lt (by have h := j.rev.isLt; omega) (by have h := j.rev.isLt; omega)
  · rw [mul_comm]
    exact coefficients_inverse ξ hξ.pow_eq_one j

theorem bernoulli_values :
    PeanoQuadrature.B2 (shift (0:Fin 4)) = (1/150:ℝ) ∧
    PeanoQuadrature.B2 (shift (1:Fin 4)) = (-11/150:ℝ) ∧
    PeanoQuadrature.B2 (shift (2:Fin 4)) = (-11/150:ℝ) ∧
    PeanoQuadrature.B2 (shift (3:Fin 4)) = (1/150:ℝ) := by
  norm_num [PeanoQuadrature.B2,shift]

theorem weighted_endpoint (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) :
    (∑ j : Fin 4, (PeanoQuadrature.B2 (shift j):ℂ)*coefficients ξ j/(1-coefficients ξ j)) = 1/15 := by
  have h0 := coefficient_pair ξ hξ 0
  have h1 := coefficient_pair ξ hξ 1
  change coefficients ξ 0/(1-coefficients ξ 0)+coefficients ξ 3/(1-coefficients ξ 3) = -1 at h0
  change coefficients ξ 1/(1-coefficients ξ 1)+coefficients ξ 2/(1-coefficients ξ 2) = -1 at h1
  simp only [Fin.sum_univ_four,bernoulli_values.1,bernoulli_values.2.1,
    bernoulli_values.2.2.1,bernoulli_values.2.2.2]
  push_cast
  linear_combination (1/150:ℂ)*h0-(11/150:ℂ)*h1

def residual (ξ y : ℂ) : ℂ := (1/2:ℂ)*∑ j : Fin 4,
  (PeanoQuadrature.B2 (shift j):ℂ)*coefficients ξ j/(1-coefficients ξ j*y)

theorem correction_decomposition (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) :
    correction ξ z = -z/30+z*Complex.exp (-z)*residual ξ (Complex.exp (-z)) := by
  have he : correction ξ z = z/2 *
      ((Complex.exp (-z))*∑ j : Fin 4, (PeanoQuadrature.B2 (shift j):ℂ)*coefficients ξ j/
          (1-coefficients ξ j*Complex.exp (-z))-
        ∑ j : Fin 4, (PeanoQuadrature.B2 (shift j):ℂ)*coefficients ξ j/(1-coefficients ξ j)) := by
    unfold correction
    congr 1
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,weighted_endpoint ξ hξ]
  unfold residual
  ring

end
end Borwein.CorrectionCancellation
