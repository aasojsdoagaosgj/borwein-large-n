import Borwein.EMIntegralBounds
import Mathlib.Topology.Algebra.Polynomial

namespace Borwein.FiniteMajorArc
noncomputable section
open Complex Set MeasureTheory CombinedAmplitude FiveRootProductExpansion EMExponentialRemainder
  EMUniformBounds EMIntegralBounds GaussianNormalization SmallBoxPhaseDecay RadialDerivatives

def integrand (ζ : ℂ) (a n : ℕ) (τ t : ℝ) : ℂ :=
  Complex.exp ((n:ℂ)*(-PhaseIntegral.complexR (τ:ℂ)+(firstDerivative τ:ℂ)*(t:ℂ)*I))*
    ∑ j : Fin 4, phaseWeight ζ a j*Polynomial.eval₂ (Int.castRingHom ℂ)
      (point (coefficients ζ j) ((τ:ℂ)-(t:ℂ)*I) n) (Borwein.polynomial n)

def normalizedError (ζ : ℂ) (a n : ℕ) (τ h N : ℝ) : ℝ :=
  errorCoefficient ζ a τ/n+‖psi ζ a (τ:ℂ)‖*Real.exp (-(n:ℝ)*secondDerivative τ*h^2/2)+
    thetaBudget ζ a τ h/((n:ℝ)*Real.sqrt (39/50:ℝ))+
    residualBudget τ h N/((n:ℝ)^2*Real.sqrt (39/50:ℝ))

theorem integrand_continuous (ζ : ℂ) (a n : ℕ) (τ : ℝ) :
    Continuous (integrand ζ a n τ) := by
  unfold integrand point
  fun_prop

theorem integrand_decomposition (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ t : ℝ)
    (hn : 0 < n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (ht : |t| ≤ 2/5) :
    integrand ζ a n τ t =
      (psi ζ a ((τ:ℂ)-(t:ℂ)*I)+theta ζ a ((τ:ℂ)-(t:ℂ)*I)/(n:ℂ)+
        combinedRemainder ζ a n ((τ:ℂ)-(t:ℂ)*I))*Complex.exp (saddlePhase n τ t) := by
  unfold integrand
  rw [four_root_decomposition ζ _ hζ a n hn (by simpa using hτ0) (by simpa using hτ1) (by simpa using ht)]
  rw [← mul_assoc,← Complex.exp_add]
  have he : (n:ℂ)*(-PhaseIntegral.complexR (τ:ℂ)+(firstDerivative τ:ℂ)*(t:ℂ)*I)+
      (n:ℂ)*PhaseIntegral.complexR ((τ:ℂ)-(t:ℂ)*I) = saddlePhase n τ t := by
    unfold saddlePhase
    push_cast
    ring
  rw [he,mul_comm]

theorem integral_difference (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ h : ℝ)
    (hn : 0 < n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    (∫ t in -h..h, integrand ζ a n τ t)-
      (∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t)) =
    ∫ t in -h..h, (theta ζ a ((τ:ℂ)-(t:ℂ)*I)/(n:ℂ)+
      combinedRemainder ζ a n ((τ:ℂ)-(t:ℂ)*I))*Complex.exp (saddlePhase n τ t) := by
  have hi := (integrand_continuous ζ a n τ).intervalIntegrable (μ := volume) (-h) h
  have ha := SymmetricGaussian.psi_continuousOn_contour ζ hζ a τ h hτ0 hh1
  have hf := ActualPhaseContinuity.phase_exp_continuousOn n τ h hτ0 hh1
  have hip : IntervalIntegrable (fun t => psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t))
      volume (-h) h := (ha.mul hf).intervalIntegrable_of_Icc (μ := volume) (by linarith : -h ≤ h)
  rw [← intervalIntegral.integral_sub hi hip]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (-h) h := by simpa [uIcc_of_le (by linarith : -h ≤ h)] using ht
  dsimp only
  rw [integrand_decomposition ζ hζ a n τ t hn hτ0 hτ1 ((abs_le.mpr ht').trans hh1)]
  ring

theorem normalized_em_difference (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ h N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, integrand ζ a n τ t)-
      (∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t))‖/scale n τ ≤
      thetaBudget ζ a τ h/((n:ℝ)*Real.sqrt (39/50:ℝ))+
        residualBudget τ h N/((n:ℝ)^2*Real.sqrt (39/50:ℝ)) := by
  have hn0 : 0 < (n:ℝ) := hN.trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  rw [integral_difference ζ hζ a n τ h hnNat hτ0 hτ1 hh0 hh1]
  have hb := normalized_bounded_integral
    (fun t => theta ζ a ((τ:ℂ)-(t:ℂ)*I)/(n:ℂ)+combinedRemainder ζ a n ((τ:ℂ)-(t:ℂ)*I))
    n τ h (thetaBudget ζ a τ h/n+residualBudget τ h N/(n:ℝ)^2) hn0 hτ0 hh0 hh1
    (by have hT := thetaBudget_nonneg ζ a τ h hh0; unfold residualBudget; positivity) (by
      intro t ht
      apply (norm_add_le _ _).trans
      apply add_le_add
      · rw [norm_div,Complex.norm_natCast]
        exact div_le_div_of_nonneg_right
          (theta_contour_bound ζ hζ a τ h t hτ0 hh0 hh1 (abs_le.mpr ht)) hn0.le
      · exact combined_remainder_uniform ζ hζ a n τ h N t hN hn hτ0 hτ1 hh0 hh1 (abs_le.mpr ht))
  simpa only [add_div,div_div] using hb

theorem normalized_major_arc (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ h N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5) :
    ‖(∫ t in -h..h, integrand ζ a n τ t)-psi ζ a (τ:ℂ)*(scale n τ:ℂ)‖/scale n τ ≤
      normalizedError ζ a n τ h N := by
  have hn0 := hN.trans_le hn
  have hem := normalized_em_difference ζ hζ a n τ h N hN hn hτ0 hτ1 hh0 hh1
  have hg := FullGaussianReplacement.full_normalized_replacement ζ hζ a n τ h hn0 hτ0 hh0 hh1
  let J : ℂ := ∫ t in -h..h, integrand ζ a n τ t
  let P : ℂ := ∫ t in -h..h, psi ζ a ((τ:ℂ)-(t:ℂ)*I)*Complex.exp (saddlePhase n τ t)
  let A : ℂ := psi ζ a (τ:ℂ)*(scale n τ:ℂ)
  have htri : ‖J-A‖ ≤ ‖J-P‖+‖P-A‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (J-P) (P-A)
  have hd := div_le_div_of_nonneg_right htri (scale_pos n τ hn0).le
  rw [add_div] at hd
  change ‖J-A‖/scale n τ ≤ _
  unfold normalizedError
  have hb := hd.trans (add_le_add hem hg)
  convert! hb using 1
  ring

end
end Borwein.FiniteMajorArc
