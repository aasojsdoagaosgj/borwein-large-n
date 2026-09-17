import Borwein.ComplexMainIntegral
import Borwein.ComplexKernelBridge

namespace Borwein.MainTermIdentification
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory LogFactorDerivatives FiveRootProductExpansion FifthRootLogarithm

def lambda (ξ z : ℂ) : ℂ := ∑ j : Fin 4, PeanoQuadrature.B1 (shift j) •
  (Complex.log (1-coefficients ξ j*Complex.exp (-z))-Complex.log (1-coefficients ξ j))

def amplitude (ξ z : ℂ) : ℂ := Complex.exp (lambda ξ z)

def correction (ξ z : ℂ) : ℂ := z/2 * ∑ j : Fin 4,
  (PeanoQuadrature.B2 (shift j):ℂ)*
  (coefficients ξ j*Complex.exp (-z)/(1-coefficients ξ j*Complex.exp (-z))-
    coefficients ξ j/(1-coefficients ξ j))

theorem lambda_eq_endpoints (ξ z : ℂ) : lambda ξ z =
    ∑ j : Fin 4, PeanoQuadrature.B1 (shift j) • (f0 (coefficients ξ j) z 1-f0 (coefficients ξ j) z 0) := by
  simp [lambda,f0,kernel,w]

theorem correction_eq_endpoints (ξ z : ℂ) : correction ξ z =
    ∑ j : Fin 4, (PeanoQuadrature.B2 (shift j)/2) • (f1 (coefficients ξ j) z 1-f1 (coefficients ξ j) z 0) := by
  unfold correction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [f1,kernel,w,Algebra.smul_def]
  ring

theorem fourMain_identification (ξ z : ℂ) (n : ℕ) :
    fourMain (coefficients ξ) z n = (n:ℂ)*rootIntegral ξ z+lambda ξ z+correction ξ z/(n:ℂ) := by
  rw [lambda_eq_endpoints,correction_eq_endpoints]
  unfold fourMain mainTerm rootIntegral
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_div]
  congr 2
  funext j
  simp [Algebra.smul_def,div_eq_mul_inv,mul_inv_rev]
  ring

theorem fourMain_small_box (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (n : ℕ) :
    fourMain (coefficients ξ) z n = (n:ℂ)*PhaseIntegral.complexR z+lambda ξ z+correction ξ z/(n:ℂ) := by
  rw [fourMain_identification,ComplexMainIntegral.rootIntegral_eq_complexR ξ z hξ hz hi]

theorem small_box_expansion (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) (n : ℕ) (hn : 0 < n) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n) =
      Complex.exp ((n:ℂ)*PhaseIntegral.complexR z)*amplitude ξ z*
        Complex.exp (correction ξ z/(n:ℂ)+fourRemainder (coefficients ξ) z n) ∧
    ‖fourRemainder (coefficients ξ) z n‖ ≤ 3400/(n:ℝ)^2 := by
  have h := FifthRootSeparation.small_box_expansion ξ z hξ hz0 hz1 hi n hn
  constructor
  · rw [h.1,fourMain_small_box ξ z hξ hz0 hi n]
    simp only [amplitude,Complex.exp_add]
    ring
  · exact h.2

theorem lambda_zero (ξ : ℂ) : lambda ξ 0 = 0 := by simp [lambda]
theorem amplitude_zero (ξ : ℂ) : amplitude ξ 0 = 1 := by simp [amplitude,lambda_zero]
theorem correction_zero (ξ : ℂ) : correction ξ 0 = 0 := by simp [correction]

theorem lambda_real_re (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    (lambda ξ (τ:ℂ)).re = 0 := by
  have hp (j : Fin 4) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
      (f0 (coefficients ξ j.rev) (τ:ℂ) x).re = (f0 (coefficients ξ j) (τ:ℂ) x).re := by
    rw [conjugate_coefficient ξ hξ.pow_eq_one,
      real_log_conjugate _ τ x (coefficient_slit ξ _ hξ hτ (by norm_num) j x hx)]
    rfl
  have h00 := hp 0 0 (by norm_num)
  have h01 := hp 0 1 (by norm_num)
  have h10 := hp 1 0 (by norm_num)
  have h11 := hp 1 1 (by norm_num)
  change (f0 (coefficients ξ 3) (τ:ℂ) 0).re = (f0 (coefficients ξ 0) (τ:ℂ) 0).re at h00
  change (f0 (coefficients ξ 3) (τ:ℂ) 1).re = (f0 (coefficients ξ 0) (τ:ℂ) 1).re at h01
  change (f0 (coefficients ξ 2) (τ:ℂ) 0).re = (f0 (coefficients ξ 1) (τ:ℂ) 0).re at h10
  change (f0 (coefficients ξ 2) (τ:ℂ) 1).re = (f0 (coefficients ξ 1) (τ:ℂ) 1).re at h11
  rw [lambda_eq_endpoints]
  norm_num [Fin.sum_univ_four,shift,PeanoQuadrature.B1,Complex.add_re,
    Complex.sub_re,Complex.smul_re]
  linarith

theorem amplitude_real_norm (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖amplitude ξ (τ:ℂ)‖ = 1 := by
  rw [amplitude,Complex.norm_exp,lambda_real_re ξ hξ τ hτ,Real.exp_zero]

theorem small_box_expansion_kernelR (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz0 : 0 < z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) (n : ℕ) (hn : 0 < n) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n) =
      Complex.exp ((n:ℂ)*LogKernel.kernelR z)*amplitude ξ z*
        Complex.exp (correction ξ z/(n:ℂ)+fourRemainder (coefficients ξ) z n) ∧
    ‖fourRemainder (coefficients ξ) z n‖ ≤ 3400/(n:ℝ)^2 := by
  simpa only [ComplexKernelBridge.complexR_eq_kernelR z hz0] using
    small_box_expansion ξ z hξ hz0.le hz1 hi n hn

end
end Borwein.MainTermIdentification
