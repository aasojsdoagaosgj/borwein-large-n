import Borwein.CharacteristicLogBounds
import Borwein.SmallBoxPhaseDecay

namespace Borwein.CharacteristicPhaseBridge
noncomputable section
open scoped BigOperators
open Complex CenteredCharacteristic CharacteristicLogDerivatives PhaseGap PhaseIntegral RadialMoments

theorem mean_le_two (y : ℝ) (hy : 0 ≤ y) : mean y ≤ 2 := by
  have h4 : Real.exp (-4*y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h31 : Real.exp (-3*y) ≤ Real.exp (-y) := Real.exp_le_exp.mpr (by linarith)
  simp only [neg_mul] at h4 h31
  unfold mean
  apply (div_le_iff₀ (moment_zero_pos y)).mpr
  norm_num [RadialMoments.moment,Fin.sum_univ_five]
  nlinarith

theorem uncentered_identity (y t : ℝ) :
    PhaseGap.amplitude (radialWeight y) (fun j => (j:ℝ)*t) =
      unit (t*mean y)*characteristic y t := by
  rw [PhaseGap.amplitude_eq_exp_sum]
  unfold characteristic CenteredCharacteristic.moment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero,mul_one]
  unfold unit CentralMoments.centered
  rw [mul_left_comm,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem characteristic_real_pos (y t : ℝ) (ht : |t| ≤ 2/5) :
    0 < (characteristic y t).re := by
  have hs := pow_le_pow_left₀ (abs_nonneg t) ht 2
  rw [sq_abs] at hs
  have hv := mul_le_mul_of_nonneg_left (CentralMoments.variance_le_four y) (sq_nonneg t)
  have hr := characteristic_real_lower y t
  nlinarith

theorem log_density_identity (y t : ℝ) (hy : 0 ≤ y) (ht : |t| ≤ 2/5) :
    Complex.log (fiveSum ((y:ℂ)-(t:ℂ)*I)) =
      (Real.log (radialSum y):ℂ)+(t*mean y:ℝ)*I+logValue y t := by
  have hn := characteristic_ne_zero y t ht
  have hrad : 0 < radialSum y := radialDenominator_pos y
  have ha := Complex.abs_arg_le_pi_div_two_iff.mpr (characteristic_real_pos y t ht).le
  have hm := mean_le_two y hy
  have hm0 := mean_nonneg y
  have htm : |t*mean y| ≤ 4/5 := by
    rw [abs_mul,abs_of_nonneg hm0]
    nlinarith [abs_nonneg t]
  let q : ℂ := (Real.log (radialSum y):ℂ)+(t*mean y:ℝ)*I+logValue y t
  have hqi : |q.im| ≤ 4/5+Real.pi/2 := by
    have h := (abs_add_le (t*mean y) (characteristic y t).arg).trans (add_le_add htm ha)
    simpa [q,logValue,jet_zero,Complex.log] using h
  have he : Complex.exp q = fiveSum ((y:ℂ)-(t:ℂ)*I) := by
    have hp := phase_eq_fiveSum_div y t 1
    simp only [phase,mul_one,Complex.ofReal_one] at hp
    rw [uncentered_identity] at hp
    have hd : (radialSum y:ℂ) ≠ 0 := by exact_mod_cast hrad.ne'
    have hp' := (eq_div_iff hd).mp hp
    dsimp only [q]
    rw [Complex.exp_add,Complex.exp_add]
    rw [← Complex.ofReal_exp,Real.exp_log hrad]
    rw [logValue,jet_zero,Complex.exp_log hn]
    simpa only [unit,mul_assoc,mul_comm,mul_left_comm] using hp'
  have hπ := Real.pi_gt_three
  have hq := abs_le.mp hqi
  have hl := Complex.log_exp (x := q) (by linarith [hq.1]) (by linarith [hq.2])
  rw [he] at hl
  exact hl

theorem characteristic_line_continuous (τ t : ℝ) :
    Continuous (fun x : ℝ => characteristic (τ*x) (t*x)) := by
  unfold characteristic CenteredCharacteristic.moment unit CentralMoments.centered
  fun_prop

theorem log_density_continuousOn (τ t : ℝ) (ht : |t| ≤ 2/5) :
    ContinuousOn (fun x : ℝ => logValue (τ*x) (t*x)) (Set.Icc 0 1) := by
  simp only [logValue,jet_zero]
  apply (characteristic_line_continuous τ t).continuousOn.clog
  intro x hx
  apply characteristic_slit
  rw [abs_mul,abs_of_nonneg hx.1]
  nlinarith [abs_nonneg t,hx.2]

theorem complexR_centered_integral (τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    complexR ((τ:ℂ)-(t:ℂ)*I) = (radialR τ:ℂ)-
      (t:ℂ)*(RadialDerivatives.firstDerivative τ:ℂ)*I+
      ∫ x in (0:ℝ)..1, logValue (τ*x) (t*x) := by
  have hc : Continuous (fun x : ℝ => (Real.log (radialSum (τ*x)):ℂ)) := by
    exact Complex.continuous_ofReal.comp (continuous_log_radialSum τ)
  have hm : Continuous (fun x : ℝ => (-(t:ℂ)*I)*(RadialDerivatives.firstDensity τ x:ℂ)) := by
    exact continuous_const.mul (Complex.continuous_ofReal.comp (RadialDerivatives.continuous_firstDensity τ))
  have hl : IntervalIntegrable (fun x : ℝ => logValue (τ*x) (t*x)) MeasureTheory.volume 0 1 :=
    (log_density_continuousOn τ t ht).intervalIntegrable_of_Icc (by norm_num)
  have hcm : IntervalIntegrable (fun x : ℝ => (Real.log (radialSum (τ*x)):ℂ)+
      (-(t:ℂ)*I)*(RadialDerivatives.firstDensity τ x:ℂ)) MeasureTheory.volume 0 1 :=
    (hc.add hm).intervalIntegrable 0 1
  have he : complexR ((τ:ℂ)-(t:ℂ)*I) = ∫ x in (0:ℝ)..1,
      ((Real.log (radialSum (τ*x)):ℂ)+ (-(t:ℂ)*I)*(RadialDerivatives.firstDensity τ x:ℂ))+
      logValue (τ*x) (t*x) := by
    unfold complexR
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Set.Icc (0:ℝ) 1 := by simpa using hx
    have htx : |t*x| ≤ 2/5 := by
      rw [abs_mul,abs_of_nonneg hx'.1]
      nlinarith [abs_nonneg t,hx'.2]
    have h := log_density_identity (τ*x) (t*x) (mul_nonneg hτ hx'.1) htx
    dsimp only
    rw [show ((τ:ℂ)-(t:ℂ)*I)*(x:ℂ) = ((τ*x:ℝ):ℂ)-((t*x:ℝ):ℂ)*I by push_cast; ring]
    rw [h]
    unfold RadialDerivatives.firstDensity
    push_cast
    ring
  rw [he,intervalIntegral.integral_add hcm hl,
    intervalIntegral.integral_add (hc.intervalIntegrable 0 1) (hm.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,intervalIntegral.integral_ofReal]
  change (radialR τ:ℂ)+(-(t:ℂ)*I)*(RadialDerivatives.firstDerivative τ:ℂ)+_ = _
  ring

theorem saddle_phase_integral (n τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    SmallBoxPhaseDecay.saddlePhase n τ t =
      (n:ℂ)*(∫ x in (0:ℝ)..1, logValue (τ*x) (t*x)) := by
  unfold SmallBoxPhaseDecay.saddlePhase
  rw [complexR_centered_integral τ t hτ ht,SmallBoxPhaseDecay.complexR_real]
  ring

end
end Borwein.CharacteristicPhaseBridge
