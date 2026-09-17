import Borwein.CombinedGaussianIntegral

namespace Borwein.GaussianNormalization
noncomputable section
open Complex CombinedGaussianError CombinedGaussianIntegral CombinedAmplitude
  AmplitudeTaylor ActualPhaseTaylor RadialDerivatives SmallBoxPhaseDecay

def scale (n τ : ℝ) : ℝ := Real.sqrt (2*Real.pi/(n*secondDerivative τ))
def coreBudget (ζ : ℂ) (a : ℕ) (τ : ℝ) : ℝ :=
  ‖psi ζ a (τ:ℂ)‖*(240*W 4 τ/(32*(39/100:ℝ)^2*(secondDerivative τ)^2)+
    2645*(W 3 τ)^2/(192*(39/100:ℝ)^3*(secondDerivative τ)^3))+
  4*(23*a1 τ*W 3 τ/(8*(39/100:ℝ)^2*(secondDerivative τ)^2)+a2 τ/(2*(39/100:ℝ)*secondDerivative τ))
def errorCoefficient (ζ : ℂ) (a : ℕ) (τ : ℝ) : ℝ := coreBudget ζ a τ/Real.sqrt (39/50:ℝ)

theorem scale_pos (n τ : ℝ) (hn : 0 < n) : 0 < scale n τ := by
  unfold scale
  apply Real.sqrt_pos.mpr
  exact div_pos (mul_pos (by norm_num) Real.pi_pos) (mul_pos hn (secondDerivative_pos τ))

theorem coefficient_nonneg (ζ : ℂ) (a : ℕ) (τ : ℝ) : 0 ≤ errorCoefficient ζ a τ := by
  have hV := (secondDerivative_pos τ).le
  have hW3 := W_nonneg 3 τ
  have hW4 := W_nonneg 4 τ
  have ha1 := (amplitude_budgets_nonneg τ).1
  have ha2 := (amplitude_budgets_nonneg τ).2
  unfold errorCoefficient coreBudget
  positivity

theorem sqrt_rate_identity (n τ : ℝ) (hn : 0 < n) :
    Real.sqrt (Real.pi/rate n τ)*Real.sqrt (39/50:ℝ) = scale n τ := by
  have hV := (secondDerivative_pos τ).ne'
  have hn0 := hn.ne'
  have hr : 0 < rate n τ := by
    exact mul_pos (mul_pos (by norm_num) hn) (secondDerivative_pos τ)
  rw [← Real.sqrt_mul (le_of_lt (div_pos Real.pi_pos hr))]
  unfold scale
  congr 1
  unfold rate
  field_simp
  ring

theorem moment_coefficient_identity (ζ : ℂ) (a : ℕ) (n τ : ℝ) (hn : 0 < n) :
    budget2 τ/(2*rate n τ)+3*budget4 ζ a n τ/(4*(rate n τ)^2)+
      15*budget6 ζ a n τ/(8*(rate n τ)^3) = coreBudget ζ a τ/n := by
  have hV := (secondDerivative_pos τ).ne'
  have hn0 := hn.ne'
  unfold budget2 budget4 budget6 rate coreBudget
  field_simp
  ring

theorem integral_budget_identity (ζ : ℂ) (a : ℕ) (n τ : ℝ) (hn : 0 < n) :
    integralBudget ζ a n τ = scale n τ*(errorCoefficient ζ a τ/n) := by
  calc
    _ = Real.sqrt (Real.pi/rate n τ)*(coreBudget ζ a τ/n) := by
      rw [← moment_coefficient_identity ζ a n τ hn]
      unfold integralBudget
      ring
    _ = _ := by
      rw [← sqrt_rate_identity n τ hn]
      unfold errorCoefficient
      have hsq : Real.sqrt (39/50:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
      field_simp

theorem normalized_replacement (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t))-
      psi ζ a (τ:ℂ)*(∫ t in -h..h, Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t))‖ /
      scale n τ ≤ errorCoefficient ζ a τ/n := by
  apply (div_le_iff₀ (scale_pos n τ hn)).mpr
  have hb := combined_gaussian_replacement ζ hζ a n τ h hn hτ hh0 hh1
  rw [integral_budget_identity ζ a n τ hn] at hb
  simpa only [mul_comm] using hb

end
end Borwein.GaussianNormalization
