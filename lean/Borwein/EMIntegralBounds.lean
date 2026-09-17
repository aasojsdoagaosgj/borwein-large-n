import Borwein.EMUniformBounds

namespace Borwein.EMIntegralBounds
noncomputable section
open Complex Set MeasureTheory GaussianMoments CombinedAmplitude EMExponentialRemainder
  EMUniformBounds CombinedGaussianError GaussianNormalization SmallBoxPhaseDecay RadialDerivatives

theorem phase_exp_norm_bound (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖Complex.exp (saddlePhase n τ t)‖ ≤ gaussian (rate n τ) t := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simpa only [rate,neg_mul,mul_assoc] using saddle_phase_decay n τ t hn hτ ht

theorem bounded_integral (f : ℝ → ℂ) (n τ h B : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc (-h) h, ‖f t‖ ≤ B) :
    ‖∫ t in -h..h, f t*Complex.exp (saddlePhase n τ t)‖ ≤
      B*Real.sqrt (Real.pi/rate n τ) := by
  have hh : -h ≤ h := by linarith
  have hr : 0 < rate n τ := mul_pos (mul_pos (by norm_num) hn) (secondDerivative_pos τ)
  have hi : Integrable (fun t : ℝ => B*gaussian (rate n τ) t) volume :=
    (integrable_gaussian _ hr).const_mul B
  have hpoint (t : ℝ) (ht : t ∈ Icc (-h) h) :
      ‖f t*Complex.exp (saddlePhase n τ t)‖ ≤ B*gaussian (rate n τ) t := by
    rw [norm_mul]
    exact mul_le_mul (hb t ht) (phase_exp_norm_bound n τ t hn.le hτ ((abs_le.mpr ht).trans hh1))
      (norm_nonneg _) hB
  calc
    _ ≤ ∫ t in -h..h, ‖f t*Complex.exp (saddlePhase n τ t)‖ :=
      intervalIntegral.norm_integral_le_integral_norm hh
    _ ≤ ∫ t in -h..h, B*gaussian (rate n τ) t := by
      rw [intervalIntegral.integral_of_le hh,intervalIntegral.integral_of_le hh]
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi.integrableOn
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
        (fun t ht => hpoint t ⟨ht.1.le,ht.2⟩))
    _ = B*GaussianMoments.moment (rate n τ) h 0 := by
      simp [GaussianMoments.moment,intervalIntegral.integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (moment_zero_le _ _ hr hh0) hB

theorem normalized_bounded_integral (f : ℝ → ℂ) (n τ h B : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) (hB : 0 ≤ B)
    (hb : ∀ t ∈ Icc (-h) h, ‖f t‖ ≤ B) :
    ‖∫ t in -h..h, f t*Complex.exp (saddlePhase n τ t)‖/scale n τ ≤
      B/Real.sqrt (39/50:ℝ) := by
  apply (div_le_iff₀ (scale_pos n τ hn)).mpr
  have he : B/Real.sqrt (39/50:ℝ)*scale n τ = B*Real.sqrt (Real.pi/rate n τ) := by
    rw [← sqrt_rate_identity n τ hn]
    have hs : Real.sqrt (39/50:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    field_simp
  rw [he]
  exact bounded_integral f n τ h B hn hτ hh0 hh1 hB hb

theorem theta_integral_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hn : 0 < n) (hτ : 0 ≤ τ) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖∫ t in -h..h, (theta ζ a ((τ:ℂ)-(t:ℂ)*I)/(n:ℂ))*Complex.exp (saddlePhase n τ t)‖/
      scale n τ ≤ thetaBudget ζ a τ h/(n*Real.sqrt (39/50:ℝ)) := by
  have hb := normalized_bounded_integral (fun t => theta ζ a ((τ:ℂ)-(t:ℂ)*I)/(n:ℂ))
    n τ h (thetaBudget ζ a τ h/n) hn hτ hh0 hh1
    (div_nonneg (thetaBudget_nonneg ζ a τ h hh0) hn.le) (by
      intro t ht
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
      exact div_le_div_of_nonneg_right (theta_contour_bound ζ hζ a τ h t hτ hh0 hh1 (abs_le.mpr ht)) hn.le)
  simpa only [div_div] using hb

theorem remainder_integral_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ h N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖∫ t in -h..h, combinedRemainder ζ a n ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t)‖/
      scale n τ ≤ residualBudget τ h N/((n:ℝ)^2*Real.sqrt (39/50:ℝ)) := by
  have hb := normalized_bounded_integral (fun t => combinedRemainder ζ a n ((τ:ℂ)-(t:ℂ)*I))
    n τ h (residualBudget τ h N/(n:ℝ)^2) (hN.trans_le hn) hτ0 hh0 hh1
    (by unfold residualBudget; positivity) (by
      intro t ht
      exact combined_remainder_uniform ζ hζ a n τ h N t hN hn hτ0 hτ1 hh0 hh1 (abs_le.mpr ht))
  simpa only [div_div] using hb

end
end Borwein.EMIntegralBounds
