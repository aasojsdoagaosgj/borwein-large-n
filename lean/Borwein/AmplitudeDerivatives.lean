import Borwein.MainTermIdentification

namespace Borwein.AmplitudeDerivatives
noncomputable section
open scoped BigOperators
open Complex Set FiveRootProductExpansion MainTermIdentification

def radial (c z : ℂ) : ℂ := c*Complex.exp (-z)
def factor (c z : ℂ) : ℂ := 1-radial c z
def logFirst (c z : ℂ) : ℂ := radial c z/factor c z
def logSecond (c z : ℂ) : ℂ := -radial c z/(factor c z)^2

def lambdaFirst (ξ z : ℂ) : ℂ := ∑ j : Fin 4, PeanoQuadrature.B1 (LogFactorDerivatives.shift j) •
  logFirst (coefficients ξ j) z
def lambdaSecond (ξ z : ℂ) : ℂ := ∑ j : Fin 4, PeanoQuadrature.B1 (LogFactorDerivatives.shift j) •
  logSecond (coefficients ξ j) z
def amplitudeFirst (ξ z : ℂ) : ℂ := amplitude ξ z*lambdaFirst ξ z
def amplitudeSecond (ξ z : ℂ) : ℂ := amplitude ξ z*(lambdaSecond ξ z+(lambdaFirst ξ z)^2)

theorem radial_deriv (c z : ℂ) : HasDerivAt (radial c) (-radial c z) z := by
  unfold radial
  convert! (((hasDerivAt_id z).neg).cexp).const_mul c using 1 <;> simp <;> ring

theorem factor_deriv (c z : ℂ) : HasDerivAt (factor c) (radial c z) z := by
  unfold factor
  convert! (radial_deriv c z).const_sub 1 using 1 <;> ring

theorem factor_eq_kernel (c z : ℂ) : factor c z = LogFactorDerivatives.kernel c z 1 := by
  simp [factor,radial,LogFactorDerivatives.kernel,LogFactorDerivatives.w]

theorem log_deriv (c z : ℂ) (hs : factor c z ∈ Complex.slitPlane) :
    HasDerivAt (fun z => Complex.log (factor c z)) (logFirst c z) z :=
  (factor_deriv c z).clog hs

theorem log_first_deriv (c z : ℂ) (hk : factor c z ≠ 0) :
    HasDerivAt (logFirst c) (logSecond c z) z := by
  have h := (radial_deriv c z).div (factor_deriv c z) hk
  unfold logFirst logSecond
  convert! h using 1
  simp only [factor] at hk ⊢
  field_simp
  ring

theorem coefficient_slit (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (j : Fin 4) :
    factor (coefficients ξ j) z ∈ Complex.slitPlane := by
  rw [factor_eq_kernel]
  exact FifthRootLogarithm.coefficient_slit ξ z hξ hz hi j 1 (by norm_num)

theorem lambda_deriv (ξ z : ℂ) (hs : ∀ j, factor (coefficients ξ j) z ∈ Complex.slitPlane) :
    HasDerivAt (lambda ξ) (lambdaFirst ξ z) z := by
  apply HasDerivAt.fun_sum
  intro j _
  exact ((log_deriv _ z (hs j)).sub_const (Complex.log (1-coefficients ξ j))).fun_const_smul _

theorem lambda_first_deriv (ξ z : ℂ) (hk : ∀ j, factor (coefficients ξ j) z ≠ 0) :
    HasDerivAt (lambdaFirst ξ) (lambdaSecond ξ z) z := by
  apply HasDerivAt.fun_sum
  intro j _
  exact (log_first_deriv _ z (hk j)).fun_const_smul _

theorem amplitude_deriv (ξ z : ℂ) (hs : ∀ j, factor (coefficients ξ j) z ∈ Complex.slitPlane) :
    HasDerivAt (amplitude ξ) (amplitudeFirst ξ z) z := by
  exact (lambda_deriv ξ z hs).cexp

theorem amplitude_first_deriv (ξ z : ℂ) (hs : ∀ j, factor (coefficients ξ j) z ∈ Complex.slitPlane) :
    HasDerivAt (amplitudeFirst ξ) (amplitudeSecond ξ z) z := by
  have h := (amplitude_deriv ξ z hs).mul
    (lambda_first_deriv ξ z (fun j => Complex.slitPlane_ne_zero (hs j)))
  unfold amplitudeFirst amplitudeSecond
  convert! h using 1
  simp only [amplitudeFirst]
  ring

theorem small_box_derivatives (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    HasDerivAt (lambda ξ) (lambdaFirst ξ z) z ∧
    HasDerivAt (lambdaFirst ξ) (lambdaSecond ξ z) z ∧
    HasDerivAt (amplitude ξ) (amplitudeFirst ξ z) z ∧
    HasDerivAt (amplitudeFirst ξ) (amplitudeSecond ξ z) z := by
  have hs := coefficient_slit ξ z hξ hz hi
  exact ⟨lambda_deriv ξ z hs,lambda_first_deriv ξ z (fun j => Complex.slitPlane_ne_zero (hs j)),
    amplitude_deriv ξ z hs,amplitude_first_deriv ξ z hs⟩

end
end Borwein.AmplitudeDerivatives
