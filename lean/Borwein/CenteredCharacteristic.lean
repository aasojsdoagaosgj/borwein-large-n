import Borwein.CentralMoments
import Borwein.SmallAngleBounds
import Borwein.ExponentialSegment

namespace Borwein.CenteredCharacteristic
noncomputable section
open scoped BigOperators
open Complex PhaseGap RadialMoments CentralMoments

def unit (u : ℝ) : ℂ := Complex.exp ((u:ℂ)*I)
def moment (k : ℕ) (y ω : ℝ) : ℂ := ∑ j : Fin 5,
  (radialWeight y j:ℂ)*(centered y j:ℂ)^k*unit (ω*centered y j)
def characteristic (y ω : ℝ) : ℂ := moment 0 y ω

theorem unit_norm (u : ℝ) : ‖unit u‖ = 1 := by simp [unit,Complex.norm_exp]
theorem unit_re (u : ℝ) : (unit u).re = Real.cos u := by simp [unit]

theorem unit_difference (u : ℝ) : ‖unit u-1‖ ≤ |u| := by
  have h := ExponentialSegment.difference_bound ((u:ℂ)*I) 0 0 (by simp) (by simp)
  simpa [unit,norm_mul,Real.norm_eq_abs] using h

theorem moment_zero (y : ℝ) : characteristic y 0 = 1 := by
  have h := congrArg (fun x : ℝ => (x:ℂ)) (radialWeight_sum y)
  simpa [characteristic,moment,unit] using h

theorem moment_deriv (k : ℕ) (y ω : ℝ) :
    HasDerivAt (moment k y) (I*moment (k+1) y ω) ω := by
  have hi : HasDerivAt (fun u : ℝ => (u:ℂ)) 1 ω := by
    convert! Complex.ofRealCLM.hasDerivAt (x := ω) using 1
  have ht (j : Fin 5) : HasDerivAt
      (fun u => (radialWeight y j:ℂ)*(centered y j:ℂ)^k*unit (u*centered y j))
      (I*((radialWeight y j:ℂ)*(centered y j:ℂ)^(k+1)*unit (ω*centered y j))) ω := by
    unfold unit
    convert! ((((hi.mul_const (centered y j:ℂ)).mul_const I).cexp).const_mul
      ((radialWeight y j:ℂ)*(centered y j:ℂ)^k)) using 1 <;>
      simp only [Complex.ofReal_mul,pow_succ] <;> ring
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => ht j)
  convert! h using 1 <;> simp only [moment,Finset.mul_sum]

theorem moment_norm_bound (k : ℕ) (y ω : ℝ) :
    ‖moment k y ω‖ ≤ ∑ j : Fin 5, radialWeight y j*|centered y j|^k := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,unit_norm,mul_one,
    abs_of_pos (radialWeight_pos y j)]
  exact le_rfl

theorem higher_moment_bound (k : ℕ) (y ω : ℝ) :
    ‖moment (k+2) y ω‖ ≤ 4^k*variance y :=
  (moment_norm_bound (k+2) y ω).trans (absolute_moment_bound y k)

theorem first_moment_centering (y ω : ℝ) : moment 1 y ω =
    ∑ j : Fin 5, (radialWeight y j:ℂ)*(centered y j:ℂ)*(unit (ω*centered y j)-1) := by
  have h := congrArg (fun x : ℝ => (x:ℂ)) (centered_mean_zero y)
  push_cast at h
  simp only [mul_sub,mul_one,Finset.sum_sub_distrib,h,sub_zero,moment,pow_one]

theorem first_moment_bound (y ω : ℝ) : ‖moment 1 y ω‖ ≤ |ω| * variance y := by
  rw [first_moment_centering,← centered_second,Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos (radialWeight_pos y j)]
  have h := mul_le_mul_of_nonneg_left (unit_difference (ω*centered y j))
    (mul_nonneg (radialWeight_pos y j).le (abs_nonneg (centered y j)))
  calc
    _ ≤ _ := h
    _ = _ := by rw [abs_mul]; calc
      _ = |ω| * (radialWeight y j * |centered y j|^2) := by ring
      _ = _ := by rw [sq_abs]

theorem cosine_small_lower (u : ℝ) (hu : |u| ≤ 4/5) : (69/100:ℝ) ≤ Real.cos u := by
  have hh : |u/2| ≤ 2/5 := by rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hs := SmallAngleBounds.abs_sine_upper (u/2) hh
  have hsq := pow_le_pow_left₀ (abs_nonneg (Real.sin (u/2))) hs 2
  have hc := Real.cos_two_mul_eq_one_sub (u/2)
  rw [show 2*(u/2)=u by ring] at hc
  rw [sq_abs] at hsq
  nlinarith

theorem shifted_identity (y ω : ℝ) :
    characteristic y ω = unit (ω*(2-mean y))*
      PhaseGap.amplitude (radialWeight y) (fun j => ω*((j:ℝ)-2)) := by
  rw [PhaseGap.amplitude_eq_exp_sum,Finset.mul_sum]
  unfold characteristic moment
  apply Finset.sum_congr rfl
  intro j _
  simp only [pow_zero,mul_one]
  unfold unit centered
  rw [mul_left_comm,← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem characteristic_norm_lower (y ω : ℝ) (hω : |ω| ≤ 2/5) :
    (69/100:ℝ) ≤ ‖characteristic y ω‖ := by
  have hc (j : Fin 5) : (69/100:ℝ) ≤ Real.cos (ω*((j:ℝ)-2)) := by
    apply cosine_small_lower
    have hj : |(j:ℝ)-2| ≤ 2 := by
      have hj0 : (0:ℝ) ≤ j := by positivity
      have hj4 : (j:ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    rw [abs_mul]
    exact (mul_le_mul hω hj (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hr : (69/100:ℝ) ≤ (PhaseGap.amplitude (radialWeight y) (fun j => ω*((j:ℝ)-2))).re := by
    calc
      _ = ∑ j : Fin 5, radialWeight y j*(69/100) := by rw [← Finset.sum_mul,radialWeight_sum,one_mul]
      _ ≤ _ := by
        change (∑ j : Fin 5, radialWeight y j*(69/100)) ≤
          ∑ j : Fin 5, radialWeight y j*Real.cos (ω*((j:ℝ)-2))
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hc j) (radialWeight_pos y j).le
  rw [shifted_identity,norm_mul,unit_norm,one_mul]
  exact hr.trans (Complex.re_le_norm _)

theorem characteristic_ne_zero (y ω : ℝ) (hω : |ω| ≤ 2/5) : characteristic y ω ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0:ℝ) < 69/100).trans_le (characteristic_norm_lower y ω hω))

theorem characteristic_real_lower (y ω : ℝ) :
    1-ω^2*variance y/2 ≤ (characteristic y ω).re := by
  have hs : (∑ j : Fin 5, radialWeight y j*(1-(ω*centered y j)^2/2)) =
      1-ω^2*variance y/2 := by
    simp_rw [mul_sub,mul_one,mul_pow]
    rw [Finset.sum_sub_distrib,radialWeight_sum]
    congr 1
    rw [← centered_second,Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hs]
  simp only [characteristic,moment,pow_zero,mul_one,Complex.re_sum,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,unit_re]
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := ω*centered y j))
    (radialWeight_pos y j).le

theorem characteristic_slit (y ω : ℝ) (hω : |ω| ≤ 2/5) :
    characteristic y ω ∈ Complex.slitPlane := by
  have hs := pow_le_pow_left₀ (abs_nonneg ω) hω 2
  rw [sq_abs] at hs
  have hv := mul_le_mul_of_nonneg_left (variance_le_four y) (sq_nonneg ω)
  have hr := characteristic_real_lower y ω
  apply Complex.mem_slitPlane_iff.mpr
  left
  nlinarith

end
end Borwein.CenteredCharacteristic
