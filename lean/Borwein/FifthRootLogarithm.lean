import Borwein.FifthRootSeparation
import Borwein.PhaseIntegral

namespace Borwein.FifthRootLogarithm
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory LogFactorDerivatives FiveRootProductExpansion

theorem conjugate_root (ξ : ℂ) (hξ : ξ^5 = 1) : starRingEnd ℂ ξ = ξ^4 := by
  have hn := root_norm ξ hξ
  have hz : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  apply mul_right_cancel₀ hz
  rw [mul_comm (starRingEnd ℂ ξ),Complex.mul_conj,Complex.normSq_eq_norm_sq,hn,
    ← pow_succ,hξ]
  norm_num

theorem conjugate_coefficient (ξ : ℂ) (hξ : ξ^5 = 1) (j : Fin 4) :
    coefficients ξ j.rev = starRingEnd ℂ (coefficients ξ j) := by
  unfold coefficients
  rw [map_pow,conjugate_root ξ hξ]
  fin_cases j <;> norm_num [Fin.rev] <;>
    simp only [← pow_mul] <;>
    simp [show ξ^8 = ξ^3 by rw [show 8=5+3 by decide,pow_add,hξ,one_mul],
      show ξ^12 = ξ^2 by rw [show 12=5*2+2 by decide,pow_add,pow_mul,hξ,one_pow,one_mul],
      show ξ^16 = ξ by rw [show 16=5*3+1 by decide,pow_add,pow_mul,hξ,one_pow,one_mul,pow_one]]

theorem root_product (ξ y : ℂ) (hξ : IsPrimitiveRoot ξ 5) :
    (∏ j : Fin 4, (1-coefficients ξ j*y)) = ∑ k : Fin 5, y^k.val := by
  have hg := hξ.geom_sum_eq_zero (by norm_num : 1 < 5)
  norm_num [Finset.sum_range_succ] at hg
  have h5 := hξ.pow_eq_one
  have h6 : ξ^6 = ξ := by rw [show 6=5+1 by decide,pow_add,h5,one_mul,pow_one]
  have h7 : ξ^7 = ξ^2 := by rw [show 7=5+2 by decide,pow_add,h5,one_mul]
  have h8 : ξ^8 = ξ^3 := by rw [show 8=5+3 by decide,pow_add,h5,one_mul]
  have h9 : ξ^9 = ξ^4 := by rw [show 9=5+4 by decide,pow_add,h5,one_mul]
  have h10 : ξ^10 = 1 := by rw [show 10=5*2 by decide,pow_mul,h5,one_pow]
  simp only [Fin.prod_univ_four,Fin.sum_univ_five,coefficients]
  norm_num
  ring_nf
  rw [h10,h9,h8,h7,h6,h5]
  linear_combination (-y+y^2-y^3)*hg

theorem factor_product (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (x : ℝ) :
    (∏ j : Fin 4, kernel (coefficients ξ j) z x) = PhaseIntegral.fiveSum (z*(x:ℂ)) := by
  simpa [kernel,w,PhaseIntegral.fiveSum,neg_mul] using root_product ξ (Complex.exp (-z*(x:ℂ))) hξ

theorem real_kernel_conjugate (c : ℂ) (τ x : ℝ) :
    kernel (starRingEnd ℂ c) (τ:ℂ) x = starRingEnd ℂ (kernel c (τ:ℂ) x) := by
  simp [kernel,w,← Complex.ofReal_mul,← Complex.ofReal_neg,← Complex.ofReal_exp]

theorem real_log_conjugate (c : ℂ) (τ x : ℝ)
    (hs : kernel c (τ:ℂ) x ∈ Complex.slitPlane) :
    f0 (starRingEnd ℂ c) (τ:ℂ) x = starRingEnd ℂ (f0 c (τ:ℂ) x) := by
  rw [f0,real_kernel_conjugate,Complex.log_conj]
  · rfl
  · exact Complex.slitPlane_arg_ne_pi hs

theorem coefficient_slit (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (j : Fin 4) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    kernel (coefficients ξ j) z x ∈ Complex.slitPlane :=
  uniform_slit _ z (coefficients_norm ξ (root_norm ξ hξ.pow_eq_one).le j) hz (3/4)
    (by norm_num) (FifthRootSeparation.coefficient_gap ξ z hξ hi j) x hx

theorem coefficient_log_integrable (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) (j : Fin 4) :
    IntervalIntegrable (f0 (coefficients ξ j) z) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
  apply ContinuousOn.clog
  · unfold kernel w; fun_prop
  · exact coefficient_slit ξ z hξ hz hi j

def rootLog (ξ z : ℂ) (x : ℝ) : ℂ := ∑ j : Fin 4, f0 (coefficients ξ j) z x

theorem rootLog_real_im (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (τ x : ℝ) (hτ : 0 ≤ τ) (hx : x ∈ Icc (0:ℝ) 1) :
    (rootLog ξ (τ:ℂ) x).im = 0 := by
  have hp (j : Fin 4) : f0 (coefficients ξ j.rev) (τ:ℂ) x =
      starRingEnd ℂ (f0 (coefficients ξ j) (τ:ℂ) x) := by
    rw [conjugate_coefficient ξ hξ.pow_eq_one]
    exact real_log_conjugate _ τ x (coefficient_slit ξ _ hξ hτ (by norm_num) j x hx)
  have h0 := congrArg Complex.im (hp 0)
  have h1 := congrArg Complex.im (hp 1)
  norm_num [Fin.rev] at h0 h1
  change (f0 (coefficients ξ 3) (τ:ℂ) x).im = -(f0 (coefficients ξ 0) (τ:ℂ) x).im at h0
  change (f0 (coefficients ξ 2) (τ:ℂ) x).im = -(f0 (coefficients ξ 1) (τ:ℂ) x).im at h1
  simp only [rootLog,Fin.sum_univ_four,Complex.add_im]
  linarith

theorem exp_rootLog (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hi : |z.im| ≤ 2/5) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    Complex.exp (rootLog ξ z x) = PhaseIntegral.fiveSum (z*(x:ℂ)) := by
  rw [rootLog,Complex.exp_sum,← factor_product ξ z hξ x]
  apply Finset.prod_congr rfl
  intro j _
  apply Complex.exp_log
  exact norm_pos_iff.mp ((by norm_num : (0:ℝ) < 3/4).trans_le
    (FifthRootSeparation.coefficient_gap ξ z hξ hi j x hx))

theorem rootLog_real (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (τ x : ℝ) (hτ : 0 ≤ τ) (hx : x ∈ Icc (0:ℝ) 1) :
    rootLog ξ (τ:ℂ) x = (Real.log (PhaseIntegral.radialSum (τ*x)):ℂ) := by
  have him := rootLog_real_im ξ hξ τ x hτ hx
  have he := Complex.log_exp (x := rootLog ξ (τ:ℂ) x)
    (by rw [him]; exact neg_lt_zero.mpr Real.pi_pos) (by rw [him]; exact Real.pi_pos.le)
  rw [exp_rootLog ξ _ hξ (by norm_num) x hx,← Complex.ofReal_mul,PhaseIntegral.fiveSum_real] at he
  rw [← he]
  exact (Complex.ofReal_log (PhaseGap.radialDenominator_pos (τ*x)).le).symm

def rootIntegral (ξ z : ℂ) : ℂ := ∑ j : Fin 4, ∫ x in (0:ℝ)..1, f0 (coefficients ξ j) z x

theorem rootIntegral_eq_integral (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 2/5) :
    rootIntegral ξ z = ∫ x in (0:ℝ)..1, rootLog ξ z x := by
  unfold rootIntegral rootLog
  rw [intervalIntegral.integral_finset_sum]
  intro j _
  exact coefficient_log_integrable ξ z hξ hz hi j

theorem rootIntegral_real (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    rootIntegral ξ (τ:ℂ) = (PhaseIntegral.radialR τ:ℂ) := by
  rw [rootIntegral_eq_integral ξ _ hξ hτ (by norm_num),PhaseIntegral.radialR,
    ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x hx
  exact rootLog_real ξ hξ τ x hτ (by simpa using hx)

end
end Borwein.FifthRootLogarithm
