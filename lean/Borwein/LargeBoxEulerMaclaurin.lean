import Borwein.SecondEulerMaclaurin
import Borwein.LargeBoxSeparation
import Borwein.MainTermIdentification

namespace Borwein.LargeBoxEulerMaclaurin
noncomputable section
open Complex Set MeasureTheory LogFactorDerivatives FiveRootProductExpansion MainTermIdentification FifthRootLogarithm

def singleResidual (c z : ℂ) (n : ℕ) (α : ℝ) : ℂ :=
  (∑ k ∈ Finset.range n, f0 c z (((k:ℝ)+α)/n))-(n:ℝ) • (∫ x in (0:ℝ)..1, f0 c z x)-
    PeanoQuadrature.B1 α • (f0 c z 1-f0 c z 0)
def largeRemainder (ξ z : ℂ) (n : ℕ) : ℂ := ∑ j : Fin 4, singleResidual (coefficients ξ j) z n (shift j)

theorem second_continuousOn (c z : ℂ) (s : Set ℝ) (hk : ∀ x ∈ s, kernel c z x ≠ 0) :
    ContinuousOn (f2 c z) s := by
  unfold f2
  apply ContinuousOn.div
  · unfold w; fun_prop
  · unfold kernel w; fun_prop
  · intro x hx
    exact pow_ne_zero 2 (hk x hx)

theorem second_norm_bound (c z : ℂ) (x d : ℝ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re)
    (hx : 0 ≤ x) (hd : 0 < d) (hgap : d ≤ ‖kernel c z x‖) : ‖f2 c z x‖ ≤ ‖z‖^2/d^2 := by
  have hw := w_norm_le_one c z x hc hz hx
  calc
    _ = ‖z‖^2*‖w c z x‖/‖kernel c z x‖^2 := by simp [f2,norm_pow]
    _ ≤ ‖z‖^2*1/d^2 := by gcongr
    _ = _ := by ring

theorem second_integral_bound (c z : ℂ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖) :
    (∫ x in (0:ℝ)..1, ‖f2 c z x‖) ≤ ‖z‖^2/d^2 := by
  have hi : IntervalIntegrable (fun x => ‖f2 c z x‖) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using (second_continuousOn c z _ (uniform_kernel_ne_zero c z d hd hgap)).norm
  have hb := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi
    (intervalIntegrable_const (c := ‖z‖^2/d^2))
    (fun x hx => second_norm_bound c z x d hc hz hx.1 hd (hgap x hx))
  simpa using hb

theorem single_residual_bound (c z : ℂ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) :
    ‖singleResidual c z n α‖ ≤ (1/(8*(n:ℝ)))*(‖z‖^2/d^2) := by
  have hk := uniform_kernel_ne_zero c z d hd hgap
  have hs := uniform_slit c z hc hz d hd hgap
  have hb := SecondEulerMaclaurin.error_bound n hn α ha0 ha1 (f0 c z) (f1 c z) (f2 c z)
    (fun x hx => log_deriv c z x (hs x hx)) (fun x hx => first_deriv c z x (hk x hx))
    (second_continuousOn c z _ hk)
  exact hb.trans (mul_le_mul_of_nonneg_left (second_integral_bound c z hc hz d hd hgap) (by positivity))

theorem box_norm (z : ℂ) (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 6/5) : ‖z‖ ≤ 6 := by
  have hr := pow_le_pow_left₀ hz0 hz1 2
  have him := pow_le_pow_left₀ (abs_nonneg z.im) hi 2
  have hs : ‖z‖^2 = z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
  norm_num at hr him
  nlinarith [norm_nonneg z]

theorem large_remainder_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (n : ℕ) (hn : 0 < n)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 6/5) :
    ‖largeRemainder ξ z n‖ ≤ 7200/(n:ℝ) := by
  have hgap := LargeBoxSeparation.coefficient_gap ξ z hξ hi
  have hz := pow_le_pow_left₀ (norm_nonneg z) (box_norm z hz0 hz1 hi) 2
  have hs : ‖z‖^2/(1/20:ℝ)^2 ≤ 14400 := by norm_num at hz ⊢; linarith
  have hb : ‖largeRemainder ξ z n‖ ≤ ∑ _j : Fin 4, (1800:ℝ)/n := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    have he := single_residual_bound _ z (coefficients_norm ξ (root_norm ξ hξ.pow_eq_one).le j)
      hz0 (1/20) (by norm_num) (hgap j) n hn (shift j) (shift_mem j).1 (shift_mem j).2
    have hb := he.trans (mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ) ≤ 1/(8*(n:ℝ))))
    convert! hb using 1
    ring
  norm_num at hb
  convert! hb using 1
  ring

theorem exponent_identity (ξ z : ℂ) (n : ℕ) :
    fourMain (coefficients ξ) z n+fourRemainder (coefficients ξ) z n =
      (n:ℂ)*rootIntegral ξ z+lambda ξ z+largeRemainder ξ z n := by
  rw [lambda_eq_endpoints]
  unfold fourMain fourRemainder remainder mainTerm rootIntegral largeRemainder singleResidual
  simp only [Fin.sum_univ_four,Complex.real_smul,Complex.ofReal_natCast]
  ring

theorem large_box_expansion (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (n : ℕ) (hn : 0 < n)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 6/5) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n) =
      Complex.exp ((n:ℂ)*rootIntegral ξ z)*amplitude ξ z*Complex.exp (largeRemainder ξ z n) ∧
      ‖largeRemainder ξ z n‖ ≤ 7200/(n:ℝ) := by
  constructor
  · rw [polynomial_expansion ξ z hξ.pow_eq_one n hn
      (fun j => uniform_kernel_ne_zero _ _ (1/20) (by norm_num) (LargeBoxSeparation.coefficient_gap ξ z hξ hi j)),
      exponent_identity,Complex.exp_add,Complex.exp_add]
    rfl
  · exact large_remainder_bound ξ z hξ n hn hz0 hz1 hi

end
end Borwein.LargeBoxEulerMaclaurin
