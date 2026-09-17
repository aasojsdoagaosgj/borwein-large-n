import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Borwein.GaussianMoments
noncomputable section
open Set MeasureTheory

def gaussian (c t : ℝ) : ℝ := Real.exp (-c*t^2)
def moment (c h : ℝ) (k : ℕ) : ℝ := ∫ t in -h..h, t^(2*k)*gaussian c t

theorem gaussian_nonneg (c t : ℝ) : 0 ≤ gaussian c t := (Real.exp_pos _).le
theorem gaussian_even (c t : ℝ) : gaussian c (-t) = gaussian c t := by simp [gaussian]
theorem gaussian_deriv (c t : ℝ) : HasDerivAt (gaussian c) (-2*c*t*gaussian c t) t := by
  unfold gaussian
  convert! (((hasDerivAt_id t).pow 2).const_mul (-c)).exp using 1 <;>
    simp only [Pi.pow_apply,id_eq] <;> ring

theorem integrable_gaussian (c : ℝ) (hc : 0 < c) : Integrable (gaussian c) :=
  integrable_exp_neg_mul_sq hc

theorem moment_nonneg (c h : ℝ) (hh : 0 ≤ h) (k : ℕ) : 0 ≤ moment c h k := by
  apply intervalIntegral.integral_nonneg (by linarith : -h ≤ h)
  intro t _
  exact mul_nonneg (Even.pow_nonneg (even_two_mul k) t) (gaussian_nonneg c t)

theorem moment_zero_le (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    moment c h 0 ≤ Real.sqrt (Real.pi/c) := by
  have hg := integrable_gaussian c hc
  have hs : (∫ t in Ioc (-h) h, gaussian c t) ≤ ∫ t : ℝ, gaussian c t :=
    setIntegral_le_integral hg (Filter.Eventually.of_forall (gaussian_nonneg c))
  have hv : (∫ t : ℝ, gaussian c t) = Real.sqrt (Real.pi/c) := integral_gaussian c
  simpa only [moment,Nat.mul_zero,pow_zero,one_mul,
    intervalIntegral.integral_of_le (by linarith : -h ≤ h)] using hs.trans_eq hv

theorem primitive_deriv (c t : ℝ) (k : ℕ) :
    HasDerivAt (fun t => t^(2*k+1)*gaussian c t)
      (((2*k+1:ℕ):ℝ)*t^(2*k)*gaussian c t-2*c*t^(2*(k+1))*gaussian c t) t := by
  have h := ((hasDerivAt_id t).pow (2*k+1)).mul (gaussian_deriv c t)
  convert! h using 1
  simp only [Pi.pow_apply,Pi.mul_apply,id_eq,Nat.add_sub_cancel,pow_succ,mul_one]
  rw [show 2*(k+1) = 2*k+2 by omega,pow_add]
  ring

theorem moment_recurrence (c h : ℝ) (k : ℕ) :
    ((2*k+1:ℕ):ℝ)*moment c h k-2*c*moment c h (k+1) =
      2*h^(2*k+1)*gaussian c h := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc (-h) h) => primitive_deriv c t k)
    ((by unfold gaussian; fun_prop : Continuous (fun t : ℝ =>
      ((2*k+1:ℕ):ℝ)*t^(2*k)*gaussian c t-2*c*t^(2*(k+1))*gaussian c t)).intervalIntegrable (-h) h)
  have hi1 : IntervalIntegrable (fun t : ℝ => ((2*k+1:ℕ):ℝ)*t^(2*k)*gaussian c t) volume (-h) h :=
    (by unfold gaussian; fun_prop : Continuous _).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => 2*c*t^(2*(k+1))*gaussian c t) volume (-h) h :=
    (by unfold gaussian; fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi1 hi2] at he
  simp only [mul_assoc,intervalIntegral.integral_const_mul,gaussian_even] at he
  have ho : (-h)^(2*k+1) = -h^(2*k+1) := by simp [pow_add,pow_mul]
  rw [ho] at he
  unfold moment
  convert! he using 1 <;> ring

theorem moment_succ_le (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) (k : ℕ) :
    moment c h (k+1) ≤ ((2*k+1:ℕ):ℝ)/(2*c)*moment c h k := by
  have he := moment_recurrence c h k
  have hp : 0 ≤ 2*h^(2*k+1)*gaussian c h :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hh _)) (gaussian_nonneg c h)
  calc
    _ ≤ (((2*k+1:ℕ):ℝ)*moment c h k)/(2*c) := by
      apply (le_div_iff₀ (by positivity : 0 < 2*c)).mpr
      nlinarith
    _ = _ := by ring

theorem moment_two_le (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    moment c h 1 ≤ Real.sqrt (Real.pi/c)/(2*c) := by
  have h1 := moment_succ_le c h hc hh 0
  have h0 := moment_zero_le c h hc hh
  norm_num only [Nat.mul_zero,Nat.zero_add,Nat.cast_one] at h1
  calc
    _ ≤ (1/(2*c))*moment c h 0 := h1
    _ ≤ (1/(2*c))*Real.sqrt (Real.pi/c) := by gcongr
    _ = _ := by ring

theorem moment_four_le (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    moment c h 2 ≤ 3*Real.sqrt (Real.pi/c)/(4*c^2) := by
  have h1 := moment_succ_le c h hc hh 1
  norm_num at h1
  calc
    _ ≤ (3/(2*c))*moment c h 1 := h1
    _ ≤ (3/(2*c))*(Real.sqrt (Real.pi/c)/(2*c)) := by gcongr; exact moment_two_le c h hc hh
    _ = _ := by ring

theorem moment_six_le (c h : ℝ) (hc : 0 < c) (hh : 0 ≤ h) :
    moment c h 3 ≤ 15*Real.sqrt (Real.pi/c)/(8*c^3) := by
  have h1 := moment_succ_le c h hc hh 2
  norm_num at h1
  calc
    _ ≤ (5/(2*c))*moment c h 2 := h1
    _ ≤ (5/(2*c))*(3*Real.sqrt (Real.pi/c)/(4*c^2)) := by gcongr; exact moment_four_le c h hc hh
    _ = _ := by ring

end
end Borwein.GaussianMoments
