import Borwein.CotangentRemainder
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Borwein.ExponentialKernelRemainder
noncomputable section
open Complex

def normalized (z : ℂ) : ℂ := z/(2*(Real.pi:ℂ)*I)
def kernel (z : ℂ) : ℂ := 1/(Complex.exp z-1)-1/z
def kappa (r : ℝ) : ℝ := 1/2+r/(12*(1-r^2/(4*Real.pi^2)))

theorem normalized_norm (z : ℂ) : ‖normalized z‖ = ‖z‖/(2*Real.pi) := by
  simp [normalized,Real.norm_of_nonneg Real.pi_pos.le]

theorem normalized_ne_zero (z : ℂ) (hz : z ≠ 0) : normalized z ≠ 0 := by
  apply div_ne_zero hz
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact mul_ne_zero (mul_ne_zero (by norm_num) hp) I_ne_zero

theorem exp_ne_one (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 2*Real.pi) : Complex.exp z ≠ 1 := by
  have hnorm : ‖normalized z‖ < 1 := by
    rw [normalized_norm]
    exact (div_lt_one (by positivity)).mpr hz
  have hc := CotangentRemainder.unit_disk_integerComplement (normalized z) (normalized_ne_zero z hz0) hnorm
  intro he
  obtain ⟨a,ha⟩ := Complex.exp_eq_one_iff.mp he
  apply hc
  refine ⟨a,?_⟩
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [normalized,ha]
  field_simp

theorem cotangent_identity (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 2*Real.pi) :
    kernel z+1/2 = (-I/(2*(Real.pi:ℂ)))*
      ((Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*normalized z)-1/normalized z) := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : Complex.exp z-1 ≠ 0 := sub_ne_zero.mpr (exp_ne_one z hz0 hz)
  have he' : 1-Complex.exp z ≠ 0 := sub_ne_zero.mpr (exp_ne_one z hz0 hz).symm
  have hx : 2*(Real.pi:ℂ)*I*normalized z = z := by
    unfold normalized
    field_simp
  rw [Complex.cot_pi_eq_exp_ratio,hx]
  unfold kernel normalized
  field_simp
  ring_nf
  simp [Complex.I_sq]
  ring

theorem shifted_bound (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < 2*Real.pi) :
    ‖kernel z+1/2‖ ≤ ‖z‖/(12*(1-‖z‖^2/(4*Real.pi^2))) := by
  have hnorm : ‖normalized z‖ < 1 := by
    rw [normalized_norm]
    exact (div_lt_one (by positivity)).mpr hz
  have hc := CotangentRemainder.cotangent_bound (normalized z) (normalized_ne_zero z hz0) hnorm
  have hb := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 1/(2*Real.pi))
  rw [cotangent_identity z hz0 hz,norm_mul]
  have hn : ‖-I/(2*(Real.pi:ℂ))‖ = 1/(2*Real.pi) := by
    simp [Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn]
  apply hb.trans_eq
  rw [normalized_norm]
  have he : (‖z‖/(2*Real.pi))^2 = ‖z‖^2/(4*Real.pi^2) := by
    rw [div_pow,mul_pow]
    norm_num
  rw [he]
  simp only [div_eq_mul_inv,mul_inv_rev]
  have hp := Real.pi_ne_zero
  field_simp
  ring

theorem kernel_bound (z : ℂ) (hz : ‖z‖ < 2*Real.pi) : ‖kernel z‖ ≤ kappa ‖z‖ := by
  by_cases hz0 : z = 0
  · subst z
    norm_num [kernel,kappa]
  have hb := shifted_bound z hz0 hz
  have ht := norm_sub_le (kernel z+(1/2:ℂ)) (1/2:ℂ)
  norm_num at ht
  unfold kappa
  linarith

end
end Borwein.ExponentialKernelRemainder
