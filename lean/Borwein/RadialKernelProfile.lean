import Borwein.AngularKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Borwein.RadialKernelProfile
noncomputable section
open AngularKernel

def profile (u : ℝ) :=
  |Real.sin (2*u)| / (|Real.sin (u/2)| * |Real.sin (5*u/2)|)

theorem unit_distance (u : ℝ) : ‖1-circle u‖ = 2*|Real.sin (u/2)| := by
  have h := radial_distance_sq 1 u
  norm_num only [Complex.ofReal_one, one_mul, sub_self, zero_pow, zero_add] at h
  nlinarith [sq_abs (Real.sin (u/2)), norm_nonneg (1-circle u), abs_nonneg (Real.sin (u/2))]

theorem numerator_split (ρ u : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖1-((ρ:ℂ)*circle u)^4‖ ≤ 2*|Real.sin (2*u)|+(1-ρ^4) := by
  have hp : ρ^4 ≤ 1 := pow_le_one₀ hρ hρ1
  have he : 1-((ρ:ℂ)*circle u)^4 =
      (1-circle (4*u))+((1-ρ^4:ℝ):ℂ)*circle (4*u) := by
    rw [radial_pow]
    norm_num only [Nat.cast_ofNat]
    push_cast
    ring
  rw [he]
  have ht := norm_add_le (1-circle (4*u)) (((1-ρ^4:ℝ):ℂ)*circle (4*u))
  rw [unit_distance, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (sub_nonneg.mpr hp), circle_norm, mul_one,
    show 4*u/2=2*u by ring] at ht
  exact ht

theorem numerator_balanced (ρ u : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ‖1-((ρ:ℂ)*circle u)^4‖ ≤ 2*ρ^2*|Real.sin (2*u)|+(1-ρ^4) := by
  have hp : ρ^4 ≤ 1 := pow_le_one₀ hρ hρ1
  rw [radial_pow]
  norm_num only [Nat.cast_ofNat]
  have he := radial_distance_sq (ρ^4) (4*u)
  rw [show 4*u/2=2*u by ring] at he
  have ht : (2*ρ^2*|Real.sin (2*u)|)^2 = 4*ρ^4*(Real.sin (2*u))^2 := by
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have hm := mul_nonneg (sub_nonneg.mpr hp)
    (show 0 ≤ 2*ρ^2*|Real.sin (2*u)| by positivity)
  nlinarith [norm_nonneg (1-((ρ^4:ℝ):ℂ)*circle (4*u)),
    show 0 ≤ 2*ρ^2*|Real.sin (2*u)| by positivity]

theorem profile_upper (ρ u : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.kernel ((ρ:ℂ)*circle u)‖ ≤
      profile u/2+(1-ρ^4)/(4*ρ^2*|Real.sin (u/2)| * |Real.sin (5*u/2)|) := by
  have h := radial_kernel_upper ρ u hρ hu h5u
  have hn := numerator_balanced ρ u hρ.le hρ1
  have hd : 0 ≤ 4*ρ^2*|Real.sin (u/2)| * |Real.sin (5*u/2)| := by positivity
  refine h.trans ((div_le_div_of_nonneg_right hn hd).trans_eq ?_)
  unfold profile
  field_simp
  ring

theorem unit_profile (u : ℝ) :
    2*‖FiniteFourierKernel.kernel (circle u)‖ = profile u := by
  unfold FiniteFourierKernel.kernel profile
  rw [norm_div, norm_mul, norm_mul, circle_norm, one_mul, circle_pow, circle_pow]
  norm_num only [Nat.cast_ofNat]
  rw [unit_distance, unit_distance, unit_distance]
  rw [show 4*u/2=2*u by ring]
  ring

theorem finite_profile_upper (n : ℕ) (ρ u : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.finiteSum n ((ρ:ℂ)*circle u)‖ ≤
      (1+ρ^(5*n))*(profile u/2+
        (1-ρ^4)/(4*ρ^2*|Real.sin (u/2)| * |Real.sin (5*u/2)|)) := by
  have h := radial_finiteSum_upper n ρ u hρ hu h5u
  have hn := numerator_balanced ρ u hρ.le hρ1
  have hd : 0 ≤ 4*ρ^2*|Real.sin (u/2)| * |Real.sin (5*u/2)| := by positivity
  have hh := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hn hd)
    (by positivity : 0 ≤ 1+ρ^(5*n))
  refine h.trans (hh.trans_eq ?_)
  unfold profile
  field_simp
  ring

theorem sinh_correction (x D : ℝ) :
    (1-(Real.exp (-x))^4)/(4*(Real.exp (-x))^2*D) =
      Real.sinh (2*x)/(2*D) := by
  have he : Real.exp (2*x) = (Real.exp x)^2 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul x 2
  rw [Real.sinh_eq]
  simp only [Real.exp_neg, he]
  have hp := (Real.exp_pos x).ne'
  by_cases hD : D = 0
  · simp [hD]
  · field_simp
    ring

theorem exponential_profile_upper (x u : ℝ) (hx : 0 ≤ x)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.kernel ((Real.exp (-x):ℂ)*circle u)‖ ≤
      profile u/2+Real.sinh (2*x)/(2*|Real.sin (u/2)| * |Real.sin (5*u/2)|) := by
  have h := profile_upper (Real.exp (-x)) u (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)) hu h5u
  have hc := sinh_correction x (|Real.sin (u/2)| * |Real.sin (5*u/2)|)
  simp only [← mul_assoc] at hc
  rwa [hc] at h

theorem exponential_finite_upper (n : ℕ) (x u : ℝ) (hx : 0 ≤ x)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.finiteSum n ((Real.exp (-x):ℂ)*circle u)‖ ≤
      (1+(Real.exp (-x))^(5*n))*(profile u/2+
        Real.sinh (2*x)/(2*|Real.sin (u/2)| * |Real.sin (5*u/2)|)) := by
  have h := finite_profile_upper n (Real.exp (-x)) u (Real.exp_pos _)
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)) hu h5u
  have hc := sinh_correction x (|Real.sin (u/2)| * |Real.sin (5*u/2)|)
  simp only [← mul_assoc] at hc
  rwa [hc] at h

theorem uniform_profile_upper (x X u : ℝ) (hx : 0 ≤ x) (hxX : x ≤ X)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.kernel ((Real.exp (-x):ℂ)*circle u)‖ ≤
      profile u/2+Real.sinh (2*X)/(2*|Real.sin (u/2)| * |Real.sin (5*u/2)|) := by
  refine (exponential_profile_upper x u hx hu h5u).trans (add_le_add le_rfl ?_)
  apply div_le_div_of_nonneg_right
  · exact Real.sinh_le_sinh.mpr (by linarith)
  · positivity

end
end Borwein.RadialKernelProfile
