import Borwein.HigherOrderSegment
import Borwein.CharacteristicPhaseBridge

namespace Borwein.CharacteristicTaylor
noncomputable section
open scoped BigOperators
open Complex Set PhaseGap RadialMoments CentralMoments CenteredCharacteristic
  CharacteristicLogDerivatives CharacteristicLogBounds

def centralMoment (k : ℕ) (y : ℝ) : ℝ := ∑ j : Fin 5, radialWeight y j*(centered y j)^k

theorem moment_at_zero (k : ℕ) (y : ℝ) :
    CenteredCharacteristic.moment k y 0 = (centralMoment k y:ℂ) := by
  simp [CenteredCharacteristic.moment,unit,centralMoment]

theorem central_first (y : ℝ) : centralMoment 1 y = 0 := by
  simpa only [centralMoment,pow_one] using centered_mean_zero y

theorem central_second (y : ℝ) : centralMoment 2 y = variance y := by
  exact CentralMoments.centered_second y

theorem central_moment_continuous (k : ℕ) : Continuous (centralMoment k) := by
  unfold centralMoment centered
  fun_prop

theorem log_at_zero (y : ℝ) : logValue y 0 = 0 := by
  simp [logValue,jet_zero,CenteredCharacteristic.moment_zero]

theorem first_at_zero (y : ℝ) : logFirst y 0 = 0 := by
  simp [logFirst,jet,moment_at_zero,central_first]

theorem second_at_zero (y : ℝ) : logSecond y 0 = -(variance y:ℂ) := by
  have h0 : jet 0 y 0 = 1 := by rw [jet_zero,CenteredCharacteristic.moment_zero]
  simp only [logSecond,h0,div_one,one_pow]
  simp [jet,moment_at_zero,central_first,central_second]

theorem third_at_zero (y : ℝ) : logThird y 0 = -I*(centralMoment 3 y:ℂ) := by
  have h0 : jet 0 y 0 = 1 := by rw [jet_zero,CenteredCharacteristic.moment_zero]
  simp only [logThird,h0,div_one,one_pow]
  simp [jet,moment_at_zero,central_first,show I^3=-I by norm_num]

theorem log_fourth_continuousOn (y : ℝ) : ContinuousOn (logFourth y) (Icc (-(2/5:ℝ)) (2/5)) := by
  have hj (k : ℕ) : Continuous (jet k y) := continuous_iff_continuousAt.mpr
    (fun t => (jet_deriv k y t).continuousAt)
  have hn (t : ℝ) (ht : t ∈ Icc (-(2/5:ℝ)) (2/5)) : jet 0 y t ≠ 0 :=
    jet_nonzero y t (abs_le.mpr ht)
  unfold logFourth
  apply ContinuousOn.sub
  · apply ContinuousOn.add
    · apply ContinuousOn.sub
      · apply ContinuousOn.sub
        · exact (hj 4).continuousOn.div (hj 0).continuousOn hn
        · exact ((continuous_const.mul (hj 3)).mul (hj 1)).continuousOn.div
            ((hj 0).pow 2).continuousOn (fun t ht => pow_ne_zero 2 (hn t ht))
      · exact (continuous_const.mul ((hj 2).pow 2)).continuousOn.div
          ((hj 0).pow 2).continuousOn (fun t ht => pow_ne_zero 2 (hn t ht))
    · exact ((continuous_const.mul (hj 2)).mul ((hj 1).pow 2)).continuousOn.div
        ((hj 0).pow 3).continuousOn (fun t ht => pow_ne_zero 3 (hn t ht))
  · exact (continuous_const.mul ((hj 1).pow 4)).continuousOn.div
      ((hj 0).pow 4).continuousOn (fun t ht => pow_ne_zero 4 (hn t ht))

theorem segment_angle (t s : ℝ) (ht : |t| ≤ 2/5) (hs : s ∈ Icc (0:ℝ) 1) : |t*s| ≤ 2/5 := by
  rw [abs_mul,abs_of_nonneg hs.1]
  nlinarith [abs_nonneg t,hs.2]

theorem scaled_deriv (f f' : ℝ → ℂ) (k : ℕ) (t s : ℝ)
    (hd : HasDerivAt f (f' (t*s)) (t*s)) :
    HasDerivAt (fun s : ℝ => (t:ℂ)^k*f (t*s)) ((t:ℂ)^(k+1)*f' (t*s)) s := by
  have h := (hd.scomp s ((hasDerivAt_id s).const_mul t)).const_mul ((t:ℂ)^k)
  convert! h using 1
  simp only [smul_eq_mul,Complex.real_smul,pow_succ]
  ring

theorem segment_derivatives (y t s : ℝ) (ht : |t| ≤ 2/5) (hs : s ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun s => logValue y (t*s)) ((t:ℂ)*logFirst y (t*s)) s ∧
    HasDerivAt (fun s => (t:ℂ)*logFirst y (t*s)) ((t:ℂ)^2*logSecond y (t*s)) s ∧
    HasDerivAt (fun s => (t:ℂ)^2*logSecond y (t*s)) ((t:ℂ)^3*logThird y (t*s)) s ∧
    HasDerivAt (fun s => (t:ℂ)^3*logThird y (t*s)) ((t:ℂ)^4*logFourth y (t*s)) s := by
  have ha := segment_angle t s ht hs
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [Nat.zero_add,pow_zero,one_mul,pow_one] using scaled_deriv (logValue y) (logFirst y) 0 t s (log_deriv y (t*s) ha)
  · simpa only [pow_one] using scaled_deriv (logFirst y) (logSecond y) 1 t s (first_deriv y (t*s) ha)
  · exact scaled_deriv (logSecond y) (logThird y) 2 t s (second_deriv y (t*s) ha)
  · exact scaled_deriv (logThird y) (logFourth y) 3 t s (third_deriv y (t*s) ha)

theorem cubic_remainder (y t : ℝ) (ht : |t| ≤ 2/5) :
    ‖logValue y t+(variance y:ℂ)*(t:ℂ)^2/2‖ ≤ (23/6:ℝ)*variance y*|t|^3 := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) := segment_derivatives y t s ht hs
  have hc : ContinuousOn (fun s : ℝ => (t:ℂ)^3*logThird y (t*s)) (Icc 0 1) :=
    fun s hs => ((hd s hs).2.2.2).continuousAt.continuousWithinAt
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖(t:ℂ)^3*logThird y (t*s)‖ ≤ 23*variance y*|t|^3 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left (log_third_bound y (t*s) (segment_angle t s ht hs))
      (pow_nonneg (abs_nonneg t) 3)
    simpa only [mul_comm,mul_left_comm,mul_assoc] using h
  have h := HigherOrderSegment.cubic_bound
    (fun s => logValue y (t*s)) (fun s => (t:ℂ)*logFirst y (t*s))
    (fun s => (t:ℂ)^2*logSecond y (t*s)) (fun s => (t:ℂ)^3*logThird y (t*s))
    (23*variance y*|t|^3) (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2.1)
    (fun s hs => (hd s hs).2.2.1) hc hb
  simp only [mul_one,mul_zero,log_at_zero,first_at_zero,second_at_zero,sub_zero,
    Complex.real_smul] at h
  convert! h using 1
  · congr 1
    push_cast
    ring
  · ring

theorem quartic_remainder (y t : ℝ) (ht : |t| ≤ 2/5) :
    ‖logValue y t+(variance y:ℂ)*(t:ℂ)^2/2-
      (logThird y 0)*(t:ℂ)^3/6‖ ≤ 10*variance y*t^4 := by
  have hd (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) := segment_derivatives y t s ht hs
  have hmap : MapsTo (fun s : ℝ => t*s) (Icc 0 1) (Icc (-(2/5:ℝ)) (2/5)) :=
    fun s hs => abs_le.mp (segment_angle t s ht hs)
  have hc : ContinuousOn (fun s : ℝ => (t:ℂ)^4*logFourth y (t*s)) (Icc 0 1) :=
    continuousOn_const.mul ((log_fourth_continuousOn y).comp (by fun_prop) hmap)
  have hb (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
      ‖(t:ℂ)^4*logFourth y (t*s)‖ ≤ 240*variance y*|t|^4 := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs]
    have h := mul_le_mul_of_nonneg_left (log_fourth_bound y (t*s) (segment_angle t s ht hs))
      (pow_nonneg (abs_nonneg t) 4)
    simpa only [mul_comm,mul_left_comm,mul_assoc] using h
  have h := HigherOrderSegment.quartic_bound
    (fun s => logValue y (t*s)) (fun s => (t:ℂ)*logFirst y (t*s))
    (fun s => (t:ℂ)^2*logSecond y (t*s)) (fun s => (t:ℂ)^3*logThird y (t*s))
    (fun s => (t:ℂ)^4*logFourth y (t*s)) (240*variance y*|t|^4)
    (fun s hs => (hd s hs).1) (fun s hs => (hd s hs).2.1)
    (fun s hs => (hd s hs).2.2.1) (fun s hs => (hd s hs).2.2.2) hc hb
  simp only [mul_one,mul_zero,log_at_zero,first_at_zero,second_at_zero,sub_zero,
    Complex.real_smul] at h
  have ht4 : |t|^4=t^4 := by rw [show 4=2*2 by decide,pow_mul,sq_abs,← pow_mul]
  rw [ht4] at h
  convert! h using 1
  · congr 1
    push_cast
    ring
  · ring

end
end Borwein.CharacteristicTaylor
