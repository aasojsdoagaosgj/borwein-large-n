import Borwein.EMExponentialRemainder

namespace Borwein.EMUniformBounds
noncomputable section
open Complex CombinedAmplitude AmplitudeTaylor EMExponentialRemainder

def radius (τ h : ℝ) : ℝ := Real.sqrt (τ^2+h^2)
def Dstar (τ h : ℝ) : ℝ := radius τ h*((1/30:ℝ)+(8/75)*Real.exp (-τ))
def thetaBudget (ζ : ℂ) (a : ℕ) (τ h : ℝ) : ℝ :=
  radius τ h/30*(‖psi ζ a (τ:ℂ)‖+4*h*a1 τ)+(1232/1875)*radius τ h*Real.exp (-τ)
def residualBudget (τ h N : ℝ) : ℝ :=
  (154/25:ℝ)*(3400+(Dstar τ h)^2/2)*Real.exp (Dstar τ h/N+3400/N^2)

theorem radius_bound (τ h t : ℝ) (_hh : 0 ≤ h) (ht : |t| ≤ h) :
    ‖(τ:ℂ)-(t:ℂ)*I‖ ≤ radius τ h := by
  have hs := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at hs
  rw [Complex.norm_def]
  unfold radius
  apply Real.sqrt_le_sqrt
  simp [Complex.normSq_apply]
  nlinarith

theorem Dstar_nonneg (τ h : ℝ) : 0 ≤ Dstar τ h := by unfold Dstar radius; positivity

theorem thetaBudget_nonneg (ζ : ℂ) (a : ℕ) (τ h : ℝ) (hh : 0 ≤ h) :
    0 ≤ thetaBudget ζ a τ h := by
  have ha := (CombinedGaussianError.amplitude_budgets_nonneg τ).1
  unfold thetaBudget radius
  positivity

theorem correctionBudget_uniform (τ h t : ℝ) (hh : 0 ≤ h) (ht : |t| ≤ h) :
    correctionBudget ((τ:ℂ)-(t:ℂ)*I) ≤ Dstar τ h := by
  unfold correctionBudget Dstar
  simp only [Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_zero]
  exact mul_le_mul_of_nonneg_right (radius_bound τ h t hh ht) (by positivity)

theorem psi_contour_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ h t : ℝ)
    (hτ : 0 ≤ τ) (hh : h ≤ 2/5) (ht : |t| ≤ h) :
    ‖psi ζ a ((τ:ℂ)-(t:ℂ)*I)‖ ≤ ‖psi ζ a (τ:ℂ)‖+4*h*a1 τ := by
  have hv := psi_contour_variation ζ hζ a τ t hτ (ht.trans hh)
  have ha := (CombinedGaussianError.amplitude_budgets_nonneg τ).1
  have hn := norm_le_norm_sub_add (psi ζ a ((τ:ℂ)-(t:ℂ)*I)) (psi ζ a (τ:ℂ))
  nlinarith

theorem theta_contour_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ h t : ℝ)
    (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) (ht : |t| ≤ h) :
    ‖theta ζ a ((τ:ℂ)-(t:ℂ)*I)‖ ≤ thetaBudget ζ a τ h := by
  let z : ℂ := (τ:ℂ)-(t:ℂ)*I
  have hz : z.re = τ := by simp [z]
  have hr := radius_bound τ h t hh0 ht
  have hp := psi_contour_bound ζ hζ a τ h t hτ hh1 ht
  have hs := theta_small_factor ζ z hζ a (by simpa [hz] using hτ) (by simpa [z] using ht.trans hh1)
  rw [hz] at hs
  have he : theta ζ a z = (theta ζ a z+z/30*psi ζ a z)-z/30*psi ζ a z := by ring
  have hn : ‖theta ζ a z‖ ≤ ‖theta ζ a z+z/30*psi ζ a z‖+‖z‖/30*‖psi ζ a z‖ := by
    conv_lhs => rw [he]
    simpa only [norm_mul,norm_div,Complex.norm_ofNat] using norm_sub_le
      (theta ζ a z+z/30*psi ζ a z) (z/30*psi ζ a z)
  have h1 : (1232/1875:ℝ)*‖z‖*Real.exp (-τ) ≤ (1232/1875:ℝ)*radius τ h*Real.exp (-τ) := by gcongr
  have h2 : ‖z‖/30*‖psi ζ a z‖ ≤ radius τ h/30*(‖psi ζ a (τ:ℂ)‖+4*h*a1 τ) := by
    apply mul_le_mul (div_le_div_of_nonneg_right hr (by norm_num)) hp (norm_nonneg _)
    exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  unfold thetaBudget
  linarith

theorem exponentialBudget_uniform (d D n N : ℝ) (hd0 : 0 ≤ d) (hd : d ≤ D)
    (hN : 0 < N) (hn : N ≤ n) :
    exponentialBudget d 3400 n ≤ (3400+D^2/2)/n^2*Real.exp (D/N+3400/N^2) := by
  have hn0 := hN.trans_le hn
  have hD0 := hd0.trans hd
  have hsq := pow_le_pow_left₀ hd0 hd 2
  have hdn := div_le_div₀ hD0 hd hN hn
  have hnn := pow_le_pow_left₀ hN.le hn 2
  have he := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 3400) (sq_pos_of_pos hN) hnn
  unfold exponentialBudget
  apply mul_le_mul
  · apply div_le_div_of_nonneg_right _ (sq_nonneg n)
    linarith
  · exact Real.exp_le_exp.mpr (add_le_add hdn he)
  · exact (Real.exp_pos _).le
  · positivity

theorem combined_remainder_uniform (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ h N t : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) (ht : |t| ≤ h) :
    ‖combinedRemainder ζ a n ((τ:ℂ)-(t:ℂ)*I)‖ ≤ residualBudget τ h N/(n:ℝ)^2 := by
  have hn0 : 0 < n := by exact_mod_cast (hN.trans_le hn)
  have hb := combined_remainder_bound ζ ((τ:ℂ)-(t:ℂ)*I) hζ a n hn0
    (by simpa using hτ0) (by simpa using hτ1) (by simpa using ht.trans hh1)
  have hd0 : 0 ≤ correctionBudget ((τ:ℂ)-(t:ℂ)*I) := by unfold correctionBudget; positivity
  have he := exponentialBudget_uniform _ (Dstar τ h) n N hd0 (correctionBudget_uniform τ h t hh0 ht) hN hn
  have he' := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 154/25)
  apply hb.trans
  unfold residualBudget
  convert! he' using 1
  ring

end
end Borwein.EMUniformBounds
