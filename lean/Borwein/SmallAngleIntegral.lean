import Borwein.SmallAnglePole
import Borwein.DenominatorOnePositiveCertificate

set_option autoImplicit false

namespace Borwein.SmallAngleIntegral
noncomputable section
open Complex MeasureTheory SmallAnglePole SmallRadialBaseline SmoothedResonantMain

theorem value_integrable (η τ t a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => Real.log ‖value η τ t x‖) volume a b := by
  apply MeromorphicOn.intervalIntegrable_log_norm
  intro x _
  have ha : AnalyticAt ℂ (fun w : ℂ => 1-Complex.exp (-((η:ℂ)+((τ:ℂ)-(t:ℂ)*I)*w))) (x:ℂ) := by fun_prop
  exact (ha.restrictScalars.comp (Complex.ofRealCLM.analyticAt x)).meromorphicAt

theorem pole_small_angle (η τ t : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (ht : |t| ≤ 2) :
    4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ 27/25 := by
  have hfirst : (∫ x in (0:ℝ)..(1/2:ℝ), Real.log ‖value η τ t x‖) ≤ 0 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
      (value_integrable η τ t 0 (1/2)) (intervalIntegrable_const (c := (0:ℝ))) (by
        intro x hx
        have htx : |t*x| ≤ 1 := by
          rw [abs_mul,abs_of_nonneg hx.1]
          have hm := mul_le_mul_of_nonneg_right ht hx.1
          linarith [hx.2]
        have hv := value_small_upper η τ t x hη.le hτ hx.1 htx
        exact Real.log_nonpos (norm_nonneg _) hv)
    simpa using h
  have hsecond : (∫ x in (1/2:ℝ)..1, Real.log ‖value η τ t x‖) ≤ 27/100 := by
    have h := intervalIntegral.integral_mono_on (by norm_num : (1/2:ℝ) ≤ 1)
      (value_integrable η τ t (1/2) 1) (intervalIntegrable_const (c := (27/50:ℝ))) (by
        intro x hx
        have hx0 : 0 ≤ x := by linarith [hx.1]
        have htx : |t*x| ≤ 2 := by rw [abs_mul,abs_of_nonneg hx0]; nlinarith [hx.2]
        exact (Real.log_le_log (norm_pos_iff.mpr (value_ne_zero η τ t x hη hτ hx0))
          (value_upper η τ t x hη.le hτ hx0 htx)).trans log_seventeen_tenths)
    norm_num at h
    exact h
  have he := intervalIntegral.integral_add_adjacent_intervals
    (value_integrable η τ t 0 (1/2)) (value_integrable η τ t (1/2) 1)
  have hp : poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) = ∫ x in (0:ℝ)..1, Real.log ‖value η τ t x‖ := by
    simp [poleIntegral,value]
  rw [hp]
  linarith

theorem small_gap (η τ t : ℝ) (hη : 0 < η) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2) (ht : |t| ≤ 2) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) := by
  have hR := small_radial_lower τ hτ1
  have hH := pole_small_angle η τ t hη hτ0 ht
  linarith

theorem polynomial_from_gap (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1)
    (hgap : (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 PositiveCuspCertificate.eta
      ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  have hp := ResonantLimitPolynomial.denominator_one n 31147 4139 718 τ (11/2) θ PositiveCuspCertificate.eta q
    (by norm_num) hn (by norm_num) hτ0 hτ1 (by norm_num [PositiveCuspCertificate.eta])
    (by norm_num [PositiveCuspCertificate.eta]) hq
    ((DenominatorOnePositiveCertificate.radius_bound q hb).trans_lt (by linarith [Real.pi_gt_three])) hb
  apply hp.trans
  apply Real.exp_le_exp.mpr
  have hbgt := DenominatorOnePositiveCertificate.budget n q hn hb
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := (div_le_iff₀ hn0).mp (show
    4*ExponentialKernelRemainder.kappa (ResonantArgumentBounds.radiusBound 31147 4139 718 (11/2) q)*
      Real.log (2/PositiveCuspCertificate.eta)/(n:ℝ) ≤
      (1/40:ℝ)-1/4000-2*PositiveCuspCertificate.eta-10*SmoothedLogTail.tail 718 PositiveCuspCertificate.eta by linarith)
  nlinarith

theorem polynomial_small_angle (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1)
    (ht : |DirichletCover.localAngle n θ q| ≤ 2) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) :=
  polynomial_from_gap n τ θ q hn hτ0 (by linarith) hq hb
    (small_gap _ τ _ (by norm_num [PositiveCuspCertificate.eta]) hτ0 hτ1 ht)

end
end Borwein.SmallAngleIntegral
