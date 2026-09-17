import Borwein.CombinedGaussianError

namespace Borwein.CombinedGaussianIntegral
noncomputable section
open Complex Set MeasureTheory GaussianMoments CombinedAmplitude RadialDerivatives
  SmallBoxPhaseDecay CombinedGaussianError

def integralBudget (ζ : ℂ) (a : ℕ) (n τ : ℝ) : ℝ :=
  budget2 τ*Real.sqrt (Real.pi/rate n τ)/(2*rate n τ)+
  budget4 ζ a n τ*(3*Real.sqrt (Real.pi/rate n τ)/(4*(rate n τ)^2))+
  budget6 ζ a n τ*(15*Real.sqrt (Real.pi/rate n τ)/(8*(rate n τ)^3))

theorem polynomial_integral (B2 B4 B6 c h : ℝ) :
    (∫ t in -h..h, (B2*t^2+B4*t^4+B6*t^6)*gaussian c t) =
      B2*GaussianMoments.moment c h 1+B4*GaussianMoments.moment c h 2+B6*GaussianMoments.moment c h 3 := by
  have h2 : IntervalIntegrable (fun t : ℝ => B2*t^2*gaussian c t) volume (-h) h := by
    apply Continuous.intervalIntegrable
    unfold gaussian
    fun_prop
  have h4 : IntervalIntegrable (fun t : ℝ => B4*t^4*gaussian c t) volume (-h) h := by
    apply Continuous.intervalIntegrable
    unfold gaussian
    fun_prop
  have h6 : IntervalIntegrable (fun t : ℝ => B6*t^6*gaussian c t) volume (-h) h := by
    apply Continuous.intervalIntegrable
    unfold gaussian
    fun_prop
  have h24 : IntervalIntegrable (fun t : ℝ => B2*t^2*gaussian c t+B4*t^4*gaussian c t) volume (-h) h := h2.add h4
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add h24 h6,intervalIntegral.integral_add h2 h4]
  simp only [GaussianMoments.moment,mul_assoc,intervalIntegral.integral_const_mul]

theorem integral_remainder_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖∫ t in -h..h, remainder ζ a n τ t‖ ≤ integralBudget ζ a n τ := by
  have hrate : 0 < rate n τ := by
    unfold rate
    exact mul_pos (mul_pos (by norm_num) hn) (secondDerivative_pos τ)
  have hc := remainder_continuousOn ζ hζ a n τ h hτ hh1
  have hb := budgets_nonneg ζ a n τ hn.le
  have hpoly : Continuous (fun t : ℝ =>
      (budget2 τ*t^2+budget4 ζ a n τ*t^4+budget6 ζ a n τ*t^6)*gaussian (rate n τ) t) := by
    unfold gaussian
    fun_prop
  calc
    _ ≤ ∫ t in -h..h, ‖remainder ζ a n τ t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith : -h ≤ h)
    _ ≤ ∫ t in -h..h,
        (budget2 τ*t^2+budget4 ζ a n τ*t^4+budget6 ζ a n τ*t^6)*gaussian (rate n τ) t := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hc.norm.intervalIntegrable_of_Icc (by linarith)) (hpoly.intervalIntegrable (-h) h)
      intro t ht
      exact pointwise_remainder_bound ζ hζ a n τ t hn.le hτ ((abs_le.mpr ht).trans hh1)
    _ = _ := polynomial_integral _ _ _ _ _
    _ ≤ integralBudget ζ a n τ := by
      unfold integralBudget
      have h2 := mul_le_mul_of_nonneg_left (moment_two_le (rate n τ) h hrate hh0) hb.1
      have h4 := mul_le_mul_of_nonneg_left (moment_four_le (rate n τ) h hrate hh0) hb.2.1
      have h6 := mul_le_mul_of_nonneg_left (moment_six_le (rate n τ) h hrate hh0) hb.2.2
      simpa only [mul_div_assoc] using add_le_add (add_le_add h2 h4) h6

theorem integral_remainder_identity (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    (∫ t in -h..h, remainder ζ a n τ t) =
      (∫ t in -h..h, path ζ a τ t*Complex.exp (saddlePhase n τ t))-
        psi ζ a (τ:ℂ)*(∫ t in -h..h, Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) := by
  have hA := SymmetricGaussian.psi_continuousOn_contour ζ hζ a τ h hτ hh1
  have hF := ActualPhaseContinuity.phase_exp_continuousOn n τ h hτ hh1
  have hG : Continuous (fun t : ℝ => psi ζ a (τ:ℂ)*Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) := by
    unfold GaussianPhaseReplacement.exponent
    fun_prop
  have hO : Continuous (oddTerm ζ a n τ) := by
    unfold oddTerm ActualPhaseTaylor.cubicTerm GaussianPhaseReplacement.exponent
    fun_prop
  have hiF : IntervalIntegrable (fun t => path ζ a τ t*Complex.exp (saddlePhase n τ t)) volume (-h) h :=
    (hA.mul hF).intervalIntegrable_of_Icc (by linarith)
  have hiG := hG.intervalIntegrable (μ := volume) (-h) h
  have hiO := hO.intervalIntegrable (μ := volume) (-h) h
  have hiFG : IntervalIntegrable (fun t => path ζ a τ t*Complex.exp (saddlePhase n τ t)-
      psi ζ a (τ:ℂ)*Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) volume (-h) h := hiF.sub hiG
  unfold remainder
  rw [intervalIntegral.integral_sub hiFG hiO,intervalIntegral.integral_sub hiF hiG,
    odd_integral_zero,sub_zero,intervalIntegral.integral_const_mul]

theorem combined_gaussian_replacement (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t))-
      psi ζ a (τ:ℂ)*(∫ t in -h..h, Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t))‖ ≤
      integralBudget ζ a n τ := by
  have hbnd := integral_remainder_bound ζ hζ a n τ h hn hτ hh0 hh1
  rw [integral_remainder_identity ζ hζ a n τ h hτ hh0 hh1] at hbnd
  exact hbnd

end
end Borwein.CombinedGaussianIntegral
