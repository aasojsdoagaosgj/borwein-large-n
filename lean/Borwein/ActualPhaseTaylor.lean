import Borwein.CharacteristicTaylor
import Borwein.GaussianPhaseReplacement

namespace Borwein.ActualPhaseTaylor
noncomputable section
open scoped BigOperators
open Complex Set MeasureTheory RadialMoments RadialDerivatives CharacteristicLogDerivatives
  CharacteristicTaylor CharacteristicPhaseBridge SmallBoxPhaseDecay GaussianPhaseReplacement

def W (k : ℕ) (τ : ℝ) : ℝ := ∫ x in (0:ℝ)..1, x^k*variance (τ*x)
def quadraticDensity (τ t x : ℝ) : ℂ := -(t:ℂ)^2/2*(secondDensity τ x:ℂ)
def thirdDensity (τ x : ℝ) : ℂ := (x:ℂ)^3*logThird (τ*x) 0
def cubicDensity (τ t x : ℝ) : ℂ := (t:ℂ)^3/6*thirdDensity τ x
def cubicTerm (n τ t : ℝ) : ℂ := (n:ℂ)*(t:ℂ)^3/6*(∫ x in (0:ℝ)..1, thirdDensity τ x)

theorem W_nonneg (k : ℕ) (τ : ℝ) : 0 ≤ W k τ := by
  apply intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1)
  intro x hx
  exact mul_nonneg (pow_nonneg hx.1 k) (variance_pos (τ*x)).le

theorem W_two (τ : ℝ) : W 2 τ = secondDerivative τ := rfl

theorem continuous_quadratic (τ t : ℝ) : Continuous (quadraticDensity τ t) := by
  exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_secondDensity τ))

theorem continuous_third (τ : ℝ) : Continuous (thirdDensity τ) := by
  unfold thirdDensity
  simp_rw [third_at_zero]
  unfold centralMoment CentralMoments.centered
  fun_prop

theorem continuous_cubic (τ t : ℝ) : Continuous (cubicDensity τ t) :=
  continuous_const.mul (continuous_third τ)

theorem quadratic_integral (τ t : ℝ) :
    (∫ x in (0:ℝ)..1, quadraticDensity τ t x) = GaussianPhaseReplacement.exponent 1 (secondDerivative τ) t := by
  unfold quadraticDensity GaussianPhaseReplacement.exponent
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal]
  change -(t:ℂ)^2/2*(secondDerivative τ:ℂ) = _
  push_cast
  ring

theorem cubic_integral (τ t : ℝ) :
    (∫ x in (0:ℝ)..1, cubicDensity τ t x) = cubicTerm 1 τ t := by
  unfold cubicDensity cubicTerm
  rw [intervalIntegral.integral_const_mul]
  simp

theorem cubic_is_odd (n τ t : ℝ) : cubicTerm n τ (-t) = -cubicTerm n τ t := by
  unfold cubicTerm
  push_cast
  ring

theorem variance_weighted_bound (k : ℕ) (τ C : ℝ) (f : ℝ → ℂ)
    (hc : ContinuousOn f (Icc (0:ℝ) 1))
    (hb : ∀ x ∈ Icc (0:ℝ) 1, ‖f x‖ ≤ C*(x^k*variance (τ*x))) :
    ‖∫ x in (0:ℝ)..1, f x‖ ≤ C*W k τ := by
  calc
    _ ≤ ∫ x in (0:ℝ)..1, ‖f x‖ := intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ x in (0:ℝ)..1, C*(x^k*variance (τ*x)) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.norm.intervalIntegrable_of_Icc (by norm_num))
        ((by fun_prop : Continuous (fun x : ℝ => C*(x^k*variance (τ*x)))).intervalIntegrable 0 1)
      exact hb
    _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl

theorem quadratic_remainder_integral_bound (τ t : ℝ) (ht : |t| ≤ 2/5) :
    ‖∫ x in (0:ℝ)..1, logValue (τ*x) (t*x)-quadraticDensity τ t x‖ ≤
      (23/6:ℝ)*|t|^3*W 3 τ := by
  apply variance_weighted_bound 3 τ ((23/6:ℝ)*|t|^3)
  · exact (log_density_continuousOn τ t ht).sub (continuous_quadratic τ t).continuousOn
  · intro x hx
    have h := cubic_remainder (τ*x) (t*x) (segment_angle t x ht hx)
    have he : logValue (τ*x) (t*x)-quadraticDensity τ t x =
        logValue (τ*x) (t*x)+(variance (τ*x):ℂ)*((t*x:ℝ):ℂ)^2/2 := by
      unfold quadraticDensity secondDensity
      push_cast
      ring
    rw [he]
    convert! h using 1
    rw [abs_mul,abs_of_nonneg hx.1,mul_pow]
    ring

theorem cubic_remainder_integral_bound (τ t : ℝ) (ht : |t| ≤ 2/5) :
    ‖∫ x in (0:ℝ)..1, logValue (τ*x) (t*x)-quadraticDensity τ t x-cubicDensity τ t x‖ ≤
      10*t^4*W 4 τ := by
  apply variance_weighted_bound 4 τ (10*t^4)
  · exact ((log_density_continuousOn τ t ht).sub (continuous_quadratic τ t).continuousOn).sub
      (continuous_cubic τ t).continuousOn
  · intro x hx
    have h := quartic_remainder (τ*x) (t*x) (segment_angle t x ht hx)
    have he : logValue (τ*x) (t*x)-quadraticDensity τ t x-cubicDensity τ t x =
        logValue (τ*x) (t*x)+(variance (τ*x):ℂ)*((t*x:ℝ):ℂ)^2/2-
          logThird (τ*x) 0*((t*x:ℝ):ℂ)^3/6 := by
      unfold quadraticDensity secondDensity cubicDensity thirdDensity
      push_cast
      ring
    rw [he]
    convert! h using 1
    ring

theorem phase_quadratic_remainder (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖saddlePhase n τ t-GaussianPhaseReplacement.exponent n (secondDerivative τ) t‖ ≤
      (23/6:ℝ)*n*W 3 τ*|t|^3 := by
  have hl : IntervalIntegrable (fun x : ℝ => logValue (τ*x) (t*x)) volume 0 1 :=
    (log_density_continuousOn τ t ht).intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
  have he : saddlePhase n τ t-GaussianPhaseReplacement.exponent n (secondDerivative τ) t =
      (n:ℂ)*(∫ x in (0:ℝ)..1, logValue (τ*x) (t*x)-quadraticDensity τ t x) := by
    rw [saddle_phase_integral n τ t hτ ht,intervalIntegral.integral_sub hl
      ((continuous_quadratic τ t).intervalIntegrable 0 1),quadratic_integral]
    unfold GaussianPhaseReplacement.exponent
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  have h := mul_le_mul_of_nonneg_left (quadratic_remainder_integral_bound τ t ht) hn
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

theorem phase_cubic_remainder (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖saddlePhase n τ t-GaussianPhaseReplacement.exponent n (secondDerivative τ) t-cubicTerm n τ t‖ ≤
      10*n*W 4 τ*t^4 := by
  have hl : IntervalIntegrable (fun x : ℝ => logValue (τ*x) (t*x)) volume 0 1 :=
    (log_density_continuousOn τ t ht).intervalIntegrable_of_Icc (by norm_num)
  have hq := (continuous_quadratic τ t).intervalIntegrable (μ := volume) 0 1
  have hc := (continuous_cubic τ t).intervalIntegrable (μ := volume) 0 1
  have hlq : IntervalIntegrable (fun x : ℝ => logValue (τ*x) (t*x)-quadraticDensity τ t x) volume 0 1 := hl.sub hq
  have he : saddlePhase n τ t-GaussianPhaseReplacement.exponent n (secondDerivative τ) t-cubicTerm n τ t =
      (n:ℂ)*(∫ x in (0:ℝ)..1, logValue (τ*x) (t*x)-quadraticDensity τ t x-cubicDensity τ t x) := by
    rw [saddle_phase_integral n τ t hτ ht,intervalIntegral.integral_sub hlq hc,
      intervalIntegral.integral_sub hl hq,quadratic_integral,cubic_integral]
    unfold GaussianPhaseReplacement.exponent cubicTerm
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]
  have h := mul_le_mul_of_nonneg_left (cubic_remainder_integral_bound τ t ht) hn
  simpa only [mul_assoc,mul_comm,mul_left_comm] using h

theorem actual_exponential_remainder (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖Complex.exp (saddlePhase n τ t)-Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)-
      cubicTerm n τ t*Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)‖ ≤
      (10*n*W 4 τ*t^4+(529/72:ℝ)*n^2*(W 3 τ)^2*t^6)*
        GaussianMoments.gaussian ((39/100:ℝ)*n*secondDerivative τ) t := by
  exact GaussianPhaseReplacement.cubic_corrected_difference (saddlePhase n τ t) (cubicTerm n τ t)
    n (secondDerivative τ) (W 3 τ) (W 4 τ) (39/100) t hn
    (by rw [← W_two]; exact W_nonneg 2 τ) (by norm_num)
    (saddle_phase_decay n τ t hn hτ ht) (phase_quadratic_remainder n τ t hn hτ ht)
    (phase_cubic_remainder n τ t hn hτ ht)

theorem actual_exponential_difference (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖Complex.exp (saddlePhase n τ t)-Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)‖ ≤
      (23/6:ℝ)*n*W 3 τ*|t|^3*
        GaussianMoments.gaussian ((39/100:ℝ)*n*secondDerivative τ) t := by
  exact GaussianPhaseReplacement.exponential_difference (saddlePhase n τ t)
    n (secondDerivative τ) (W 3 τ) (39/100) t hn
    (by rw [← W_two]; exact W_nonneg 2 τ) (by norm_num)
    (saddle_phase_decay n τ t hn hτ ht) (phase_quadratic_remainder n τ t hn hτ ht)

theorem actual_odd_correction_integral (A0 A1 : ℂ) (n τ h : ℝ) :
    (∫ t in -h..h, (A0*cubicTerm n τ t+A1*(t:ℂ))*
      Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) = 0 := by
  have he : (fun t : ℝ => (A0*cubicTerm n τ t+A1*(t:ℂ))*
      Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) =
      (fun t : ℝ => (A0*(((n:ℂ)/6*(∫ x in (0:ℝ)..1, thirdDensity τ x))*(t:ℂ)^3)+A1*(t:ℂ))*
        Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) := by
    funext t
    unfold cubicTerm
    ring
  rw [he]
  exact GaussianPhaseReplacement.odd_correction_integral A0 A1
    ((n:ℂ)/6*(∫ x in (0:ℝ)..1, thirdDensity τ x)) n (secondDerivative τ) h

end
end Borwein.ActualPhaseTaylor
