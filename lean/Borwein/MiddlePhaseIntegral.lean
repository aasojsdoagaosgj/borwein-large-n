import Borwein.MiddlePhaseCertificate
import Mathlib.MeasureTheory.Integral.Prod

namespace Borwein.MiddlePhaseIntegral
noncomputable section
open Complex MeasureTheory Set SmallBoxPhaseDecay MiddlePhaseCertificate GaussianNormalization

theorem complexR_stronglyMeasurable : StronglyMeasurable PhaseIntegral.complexR := by
  have hc : Continuous (fun p : ℂ × ℝ => PhaseIntegral.fiveSum (p.1*(p.2:ℂ))) := by
    unfold PhaseIntegral.fiveSum
    fun_prop
  have hm := (Complex.measurable_log.comp hc.measurable).stronglyMeasurable
  have hi := hm.integral_prod_right' (ν := volume.restrict (Ioc (0:ℝ) 1))
  unfold PhaseIntegral.complexR
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact hi

theorem phase_exp_measurable (n τ : ℝ) : Measurable (fun t : ℝ => Complex.exp (saddlePhase n τ t)) := by
  have hp : Measurable (fun t : ℝ => PhaseIntegral.complexR ((τ:ℂ)-(t:ℂ)*I)) :=
    complexR_stronglyMeasurable.measurable.comp (by fun_prop)
  unfold saddlePhase
  exact Complex.continuous_exp.measurable.comp
    (measurable_const.mul ((hp.sub measurable_const).add (by fun_prop)))

theorem phase_band_integrable (n τ a b : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (hab : a ≤ b)
    (hband : ∀ t ∈ Icc a b, 2/5 ≤ |t| ∧ |t| ≤ 6/5) :
    IntervalIntegrable (fun t => Complex.exp (saddlePhase n τ t)) volume a b := by
  have hi : Integrable (fun _ : ℝ => Real.exp (-(13/250:ℝ)*n*RadialDerivatives.secondDerivative τ))
      (volume.restrict (Ioc a b)) := integrableOn_const (hs := by simp)
  have hb := hi.mono' (phase_exp_measurable n τ).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall (fun t ht =>
      band_exponential_bound n τ t hn hτ (hband t ⟨ht.1.le,ht.2⟩).1 (hband t ⟨ht.1.le,ht.2⟩).2)))
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hb

theorem bounded_norm_integral (f : ℝ → ℂ) (a b B : ℝ) (hab : a ≤ b)
    (hb : ∀ t ∈ Icc a b, ‖f t‖ ≤ B) : ‖∫ t in a..b, f t‖ ≤ (b-a)*B := by
  have hi : Integrable (fun _ : ℝ => B) (volume.restrict (Ioc a b)) := integrableOn_const (hs := by simp)
  calc
    _ ≤ ∫ t in a..b, ‖f t‖ := intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, B := by
      rw [intervalIntegral.integral_of_le hab,intervalIntegral.integral_of_le hab]
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hi
      exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall
        (fun t ht => hb t ⟨ht.1.le,ht.2⟩))
    _ = _ := by simp [intervalIntegral.integral_const,smul_eq_mul]

theorem band_integral_bound (n τ a b : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (hab : a ≤ b)
    (hband : ∀ t ∈ Icc a b, 2/5 ≤ |t| ∧ |t| ≤ 6/5) :
    ‖∫ t in a..b, Complex.exp (saddlePhase n τ t)‖ ≤
      (b-a)*Real.exp (-(13/250:ℝ)*n*RadialDerivatives.secondDerivative τ) := by
  apply bounded_norm_integral _ a b _ hab
  intro t ht
  exact band_exponential_bound n τ t hn hτ (hband t ht).1 (hband t ht).2

theorem two_sided_integral_bound (n τ : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) :
    ‖(∫ t in (-6/5:ℝ)..-2/5, Complex.exp (saddlePhase n τ t))+
      (∫ t in (2/5:ℝ)..6/5, Complex.exp (saddlePhase n τ t))‖ ≤
      (8/5:ℝ)*Real.exp (-(13/250:ℝ)*n*RadialDerivatives.secondDerivative τ) := by
  have hl := band_integral_bound n τ (-6/5) (-2/5) hn hτ (by norm_num) (by
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    constructor <;> linarith [ht.1,ht.2])
  have hr := band_integral_bound n τ (2/5) (6/5) hn hτ (by norm_num) (by
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ht)
  have hb := (norm_add_le _ _).trans (add_le_add hl hr)
  convert! hb using 1
  ring

theorem normalized_two_sided_bound (n τ : ℝ) (hn : 0 < n) (hτ : 0 ≤ τ) :
    ‖(∫ t in (-6/5:ℝ)..-2/5, Complex.exp (saddlePhase n τ t))+
      (∫ t in (2/5:ℝ)..6/5, Complex.exp (saddlePhase n τ t))‖/scale n τ ≤
      (8/5:ℝ)*Real.sqrt (n*RadialDerivatives.secondDerivative τ/(2*Real.pi))*
        Real.exp (-(13/250:ℝ)*n*RadialDerivatives.secondDerivative τ) := by
  have hs : (scale n τ)⁻¹ = Real.sqrt (n*RadialDerivatives.secondDerivative τ/(2*Real.pi)) := by
    unfold scale
    rw [← Real.sqrt_inv]
    congr 1
    simp
  have hb := div_le_div_of_nonneg_right (two_sided_integral_bound n τ hn.le hτ) (scale_pos n τ hn).le
  have he : ((8/5:ℝ)*Real.exp (-(13/250:ℝ)*n*RadialDerivatives.secondDerivative τ))/scale n τ =
      (8/5:ℝ)*Real.sqrt (n*RadialDerivatives.secondDerivative τ/(2*Real.pi))*
        Real.exp (-(13/250:ℝ)*n*RadialDerivatives.secondDerivative τ) := by
    rw [div_eq_mul_inv,hs]
    ring
  rw [he] at hb
  exact hb

end
end Borwein.MiddlePhaseIntegral
