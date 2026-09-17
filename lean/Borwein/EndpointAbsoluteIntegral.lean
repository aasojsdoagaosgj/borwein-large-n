import Borwein.EndpointGaussianBudget

set_option autoImplicit false

namespace Borwein.EndpointAbsoluteIntegral
noncomputable section
open Complex Set MeasureTheory EndpointGaussianIntegral EndpointGaussianBudget
  EndpointTaylor EndpointPhaseDecay EndpointDerivativeConstants EndpointSaddleIdentification

def envelope (v : ℝ) : ℝ := Real.sqrt (Real.pi/((97/1000)/v^3))

theorem envelope_ratio (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : envelope v ≤ (93/50)*normalizer n v := by
  have hV : 0 < variance n v := quadratic_positive n v hn hv
  have hJ := normalizer_pos n v hn hv
  have hK : 0 ≤ envelope v := Real.sqrt_nonneg _
  have hs : (envelope v)^2=Real.pi/((97/1000)/v^3) := by
    unfold envelope
    exact Real.sq_sqrt (by positivity)
  have hb : v^3*variance n v ≤ (67/100:ℝ) := (second_main_bounds n v hn hv hτ).2
  have hmul : variance n v*(envelope v)^2 ≤ (670/97)*Real.pi := by
    rw [hs]
    have hh := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (1000/97)*Real.pi)
    convert! hh using 1 <;> field_simp <;> ring
  have he : variance n v*((93/50)*normalizer n v)^2=(8649/1250)*Real.pi := by
    rw [mul_pow]
    calc
      _ = (93/50)^2*(variance n v*(normalizer n v)^2) := by ring
      _ = _ := by rw [normalizer_square n v hn hv]; ring
  have hc : variance n v*(envelope v)^2 ≤ variance n v*((93/50)*normalizer n v)^2 := by
    rw [he]
    exact hmul.trans (mul_le_mul_of_nonneg_right (by norm_num : (670/97:ℝ) ≤ 8649/1250) Real.pi_pos.le)
  have hsq : (envelope v)^2 ≤ ((93/50)*normalizer n v)^2 := by
    by_contra h
    exact (not_lt_of_ge hc) (mul_lt_mul_of_pos_left (lt_of_not_ge h) hV)
  nlinarith

theorem absolute_integral_bound (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    (∫ y in -(width v)..width v, ‖exp (phase n v y)‖) ≤ (93/50)*normalizer n v := by
  let c : ℝ := (97/1000)/v^3
  have hc : 0 < c := by dsimp [c]; positivity
  have hw : 0 ≤ width v := by unfold width; positivity
  have hP := (phase_continuous n v hn hv).cexp.norm
  have hG : Continuous (GaussianMoments.gaussian c) := by unfold GaussianMoments.gaussian; fun_prop
  have hh : (∫ y in -(width v)..width v, ‖exp (phase n v y)‖) ≤
      ∫ y in -(width v)..width v, GaussianMoments.gaussian c y := by
    apply intervalIntegral.integral_mono_on (by linarith) (hP.intervalIntegrable _ _) (hG.intervalIntegrable _ _)
    intro y hy
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hb := phase_decay n v y hn hv hτ (abs_le.mpr ⟨hy.1, hy.2⟩)
    apply hb.trans_eq
    dsimp [c]
    ring
  have hm := GaussianMoments.moment_zero_le c (width v) hc hw
  simp only [GaussianMoments.moment, Nat.mul_zero, pow_zero, one_mul] at hm
  exact (hh.trans hm).trans (envelope_ratio n v hn hv hτ)

theorem weighted_integral_error (n : ℕ) (v D : ℝ) (δ : ℝ → ℂ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hD : 0 ≤ D)
    (hδ : ContinuousOn δ (Icc (-(width v)) (width v)))
    (hb : ∀ y ∈ Icc (-(width v)) (width v), ‖δ y‖ ≤ D) :
    ‖∫ y in -(width v)..width v, exp (phase n v y)*δ y‖ ≤ (93/50)*D*normalizer n v := by
  have hw : 0 ≤ width v := by unfold width; positivity
  have hP := (phase_continuous n v hn hv).cexp
  have hI : IntervalIntegrable (fun y => ‖exp (phase n v y)*δ y‖) volume (-(width v)) (width v) :=
    (hP.continuousOn.mul hδ).norm.intervalIntegrable_of_Icc (by linarith : -(width v) ≤ width v)
  calc
    _ ≤ ∫ y in -(width v)..width v, ‖exp (phase n v y)*δ y‖ := intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ y in -(width v)..width v, D*‖exp (phase n v y)‖ := by
      apply intervalIntegral.integral_mono_on (by linarith) hI ((hP.norm.const_mul D).intervalIntegrable _ _)
      intro y hy
      rw [norm_mul, mul_comm D]
      exact mul_le_mul_of_nonneg_left (hb y hy) (norm_nonneg _)
    _ ≤ D*((93/50)*normalizer n v) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (absolute_integral_bound n v hn hv hτ) hD
    _ = _ := by ring

end
end Borwein.EndpointAbsoluteIntegral
