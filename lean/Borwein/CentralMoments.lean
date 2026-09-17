import Borwein.RadialMoments
import Borwein.RadialDerivatives

namespace Borwein.CentralMoments
noncomputable section
open scoped BigOperators
open PhaseGap RadialMoments

def centered (y : ℝ) (j : Fin 5) : ℝ := (j:ℝ)-mean y

theorem centered_abs_le (y : ℝ) (j : Fin 5) : |centered y j| ≤ 4 := by
  have hj0 : (0:ℝ) ≤ j := by positivity
  have hj4 : (j:ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
  have hm0 := mean_nonneg y
  have hm4 := mean_le_four y
  unfold centered
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem centered_mean_zero (y : ℝ) : ∑ j : Fin 5, radialWeight y j*centered y j = 0 := by
  unfold centered
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  rw [radialWeight_sum]
  have he : (∑ j : Fin 5, radialWeight y j*(j:ℝ)) = mean y := by
    simpa only [mul_comm] using (mean_eq_weighted y).symm
  rw [he]
  ring

theorem centered_second (y : ℝ) : ∑ j : Fin 5, radialWeight y j*(centered y j)^2 = variance y :=
  (variance_eq_central y).symm

theorem around_two_identity (y : ℝ) :
    (∑ j : Fin 5, radialWeight y j*((j:ℝ)-2)^2) = variance y+(mean y-2)^2 := by
  have he : (∑ j : Fin 5, radialWeight y j*((j:ℝ)-2)^2) =
      (∑ j : Fin 5, (j:ℝ)^2*radialWeight y j)-4*(∑ j : Fin 5, (j:ℝ)*radialWeight y j)+
      4*(∑ j : Fin 5, radialWeight y j) := by
    simp only [Finset.mul_sum,← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he,← second_eq_weighted,← mean_eq_weighted,radialWeight_sum]
  unfold variance
  ring

theorem variance_le_four (y : ℝ) : variance y ≤ 4 := by
  have he := around_two_identity y
  have hb : (∑ j : Fin 5, radialWeight y j*((j:ℝ)-2)^2) ≤ 4 := by
    calc
      _ ≤ ∑ j : Fin 5, radialWeight y j*4 := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (radialWeight_pos y j).le
        have hj0 : (0:ℝ) ≤ j := by positivity
        have hj4 : (j:ℝ) ≤ 4 := by exact_mod_cast Nat.le_of_lt_succ j.isLt
        nlinarith
      _ = 4 := by rw [← Finset.sum_mul,radialWeight_sum,one_mul]
  nlinarith [sq_nonneg (mean y-2)]

theorem absolute_moment_bound (y : ℝ) (k : ℕ) :
    (∑ j : Fin 5, radialWeight y j*|centered y j|^(k+2)) ≤ 4^k*variance y := by
  rw [← centered_second,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hp := pow_le_pow_left₀ (abs_nonneg (centered y j)) (centered_abs_le y j) k
  have h := mul_le_mul_of_nonneg_right hp (sq_nonneg (centered y j))
  have h' := mul_le_mul_of_nonneg_left h (radialWeight_pos y j).le
  simpa only [pow_add,sq_abs,mul_assoc,mul_comm,mul_left_comm] using h'

theorem variance_integral_le (τ : ℝ) : RadialDerivatives.secondDerivative τ ≤ 4/3 := by
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (by norm_num : (0:ℝ) ≤ 1)
    ((RadialDerivatives.continuous_secondDensity τ).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun x : ℝ => 4*x^2)).intervalIntegrable 0 1)
    (fun x _ => show RadialDerivatives.secondDensity τ x ≤ 4*x^2 from by
      unfold RadialDerivatives.secondDensity
      have h := mul_le_mul_of_nonneg_left (variance_le_four (τ*x)) (sq_nonneg x)
      simpa only [mul_comm] using h)
  norm_num [RadialDerivatives.secondDerivative,intervalIntegral.integral_const_mul,integral_pow] at h ⊢
  exact h

end
end Borwein.CentralMoments
