import Borwein.ActualPhaseTaylor
import Mathlib.Analysis.Calculus.MeanValue

namespace Borwein.ActualPhaseContinuity
noncomputable section
open Complex Set MeasureTheory RadialMoments CentralMoments CharacteristicLogDerivatives
  CharacteristicLogBounds CharacteristicPhaseBridge SmallBoxPhaseDecay

theorem log_first_bound (y t : ℝ) (ht : |t| ≤ 2/5) : ‖logFirst y t‖ ≤ 3 := by
  obtain ⟨h0,h1,_⟩ := jet_bounds y t ht
  have h := quotient_bound (jet 1 y t) (jet 0 y t) ((2/5)*variance y) (69/100) h1 h0 (by norm_num)
  change ‖logFirst y t‖ ≤ _ at h
  have hv := variance_le_four y
  norm_num at h
  nlinarith

theorem log_lipschitz_bound (y s t : ℝ) (hs : |s| ≤ 2/5) (ht : |t| ≤ 2/5) :
    ‖logValue y t-logValue y s‖ ≤ 3*|t-s| := by
  have h := (convex_Icc (-(2/5:ℝ)) (2/5)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u hu => (log_deriv y u (abs_le.mpr hu)).hasDerivWithinAt)
    (fun u hu => log_first_bound y u (abs_le.mpr hu)) (abs_le.mp hs) (abs_le.mp ht)
  simpa only [Real.norm_eq_abs] using h

theorem phase_lipschitz_bound (n τ s t : ℝ) (hτ : 0 ≤ τ) (hs : |s| ≤ 2/5) (ht : |t| ≤ 2/5) :
    ‖saddlePhase n τ t-saddlePhase n τ s‖ ≤ 3*|n| *|t-s| := by
  have his : IntervalIntegrable (fun x : ℝ => logValue (τ*x) (s*x)) volume 0 1 :=
    (log_density_continuousOn τ s hs).intervalIntegrable_of_Icc (by norm_num)
  have hit : IntervalIntegrable (fun x : ℝ => logValue (τ*x) (t*x)) volume 0 1 :=
    (log_density_continuousOn τ t ht).intervalIntegrable_of_Icc (by norm_num)
  have hb (x : ℝ) (hx : x ∈ Ioc (0:ℝ) 1) :
      ‖logValue (τ*x) (t*x)-logValue (τ*x) (s*x)‖ ≤ 3*|t-s| := by
    have hx' : x ∈ Icc (0:ℝ) 1 := ⟨hx.1.le,hx.2⟩
    have h := log_lipschitz_bound (τ*x) (s*x) (t*x)
      (CharacteristicTaylor.segment_angle s x hs hx') (CharacteristicTaylor.segment_angle t x ht hx')
    rw [← sub_mul,abs_mul,abs_of_nonneg hx.1.le] at h
    nlinarith [abs_nonneg (t-s),hx.2]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x : ℝ => logValue (τ*x) (t*x)-logValue (τ*x) (s*x))
    (a := 0) (b := 1) (C := 3*|t-s|) (by simpa using hb)
  rw [saddle_phase_integral n τ t hτ ht,saddle_phase_integral n τ s hτ hs,
    ← mul_sub,← intervalIntegral.integral_sub hit his,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have h := mul_le_mul_of_nonneg_left hi (abs_nonneg n)
  simpa [mul_comm,mul_assoc,mul_left_comm] using h

theorem phase_continuousOn (n τ h : ℝ) (hτ : 0 ≤ τ) (hh : h ≤ 2/5) :
    ContinuousOn (saddlePhase n τ) (Icc (-h) h) := by
  have hl : LipschitzOnWith ⟨3*|n|,by positivity⟩ (saddlePhase n τ) (Icc (-h) h) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro s hs t ht
    convert! phase_lipschitz_bound n τ t s hτ
      ((abs_le.mpr ht).trans hh) ((abs_le.mpr hs).trans hh) using 1 <;>
      simp only [Real.norm_eq_abs]
  exact hl.continuousOn

theorem phase_exp_continuousOn (n τ h : ℝ) (hτ : 0 ≤ τ) (hh : h ≤ 2/5) :
    ContinuousOn (fun t => Complex.exp (saddlePhase n τ t)) (Icc (-h) h) :=
  Complex.continuous_exp.comp_continuousOn (phase_continuousOn n τ h hτ hh)

end
end Borwein.ActualPhaseContinuity
