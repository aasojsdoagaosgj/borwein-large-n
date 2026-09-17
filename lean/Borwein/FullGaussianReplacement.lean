import Borwein.GaussianTail
import Borwein.GaussianNormalization

namespace Borwein.FullGaussianReplacement
noncomputable section
open Complex Set MeasureTheory CombinedAmplitude RadialDerivatives SmallBoxPhaseDecay
  GaussianNormalization CombinedGaussianIntegral

theorem gaussian_scale_identity (n τ : ℝ) (hn : 0 < n) :
    Real.sqrt (Real.pi/(n*secondDerivative τ/2)) = scale n τ := by
  unfold scale
  congr 1
  ring

theorem complex_tail_bound (n τ h : ℝ) (hn : 0 < n) (hh : 0 ≤ h) :
    ‖(∫ t in -h..h, Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t))-
      (scale n τ:ℂ)‖ ≤ scale n τ*Real.exp (-n*secondDerivative τ*h^2/2) := by
  have hc : 0 < n*secondDerivative τ/2 := by positivity [secondDerivative_pos τ]
  have ht := GaussianTail.interval_tail_bound (n*secondDerivative τ/2) h hc hh
  simp_rw [GaussianPhaseReplacement.exponent_exp]
  rw [intervalIntegral.integral_ofReal,← gaussian_scale_identity n τ hn,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  rw [gaussian_scale_identity n τ hn] at ht
  convert! ht using 1
  rw [gaussian_scale_identity n τ hn]
  congr 2 <;> ring

theorem psi_real_norm_le_four (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖psi ζ a (τ:ℂ)‖ ≤ 4 := by
  have h := weighted_sum_bound ζ hζ a
    (fun j => MainTermIdentification.amplitude (FiveRootProductExpansion.coefficients ζ j) (τ:ℂ)) 1
    (fun j => (MainTermIdentification.amplitude_real_norm _ (coefficient_primitive ζ hζ j) τ hτ).le)
  simpa only [psi,mul_one] using h

theorem full_normalized_replacement (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t))-
      psi ζ a (τ:ℂ)*(scale n τ:ℂ)‖/scale n τ ≤
      errorCoefficient ζ a τ/n+‖psi ζ a (τ:ℂ)‖*Real.exp (-n*secondDerivative τ*h^2/2) := by
  let J : ℂ := ∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t)
  let G : ℂ := ∫ t in -h..h, Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)
  let A : ℂ := psi ζ a (τ:ℂ)
  have hb := combined_gaussian_replacement ζ hζ a n τ h hn hτ hh0 hh1
  rw [integral_budget_identity ζ a n τ hn] at hb
  have ht := mul_le_mul_of_nonneg_left (complex_tail_bound n τ h hn hh0) (norm_nonneg A)
  have hs : ‖J-A*(scale n τ:ℂ)‖ ≤ ‖J-A*G‖+‖A‖*‖G-(scale n τ:ℂ)‖ := by
    have he : J-A*(scale n τ:ℂ) = (J-A*G)+A*(G-(scale n τ:ℂ)) := by ring
    rw [he]
    simpa only [norm_mul] using norm_add_le (J-A*G) (A*(G-(scale n τ:ℂ)))
  have hc := hs.trans (add_le_add hb ht)
  apply (div_le_iff₀ (scale_pos n τ hn)).mpr
  change ‖J-A*(scale n τ:ℂ)‖ ≤ _
  convert! hc using 1
  dsimp only [A]
  ring

theorem full_replacement_uniform_tail (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t))-
      psi ζ a (τ:ℂ)*(scale n τ:ℂ)‖/scale n τ ≤
      errorCoefficient ζ a τ/n+4*Real.exp (-n*secondDerivative τ*h^2/2) := by
  apply (full_normalized_replacement ζ hζ a n τ h hn hτ hh0 hh1).trans
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (psi_real_norm_le_four ζ hζ a τ hτ) (Real.exp_pos _).le)

theorem tail_from_variance_lower (n V h v δ : ℝ) (hn : 0 ≤ n) (hV : v ≤ V)
    (hδ : δ ≤ v*h^2/2) :
    4*Real.exp (-n*V*h^2/2) ≤ 4*Real.exp (-δ*n) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
  apply Real.exp_le_exp.mpr
  have hv := mul_le_mul_of_nonneg_right hV (sq_nonneg h)
  have hd : δ ≤ V*h^2/2 := by linarith
  have hp := mul_le_mul_of_nonneg_left hd hn
  nlinarith

end
end Borwein.FullGaussianReplacement
