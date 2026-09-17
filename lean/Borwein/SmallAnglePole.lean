import Borwein.SmallRadialBaseline
import Borwein.SincBounds

set_option autoImplicit false

namespace Borwein.SmallAnglePole
noncomputable section
open Complex AngularKernel SmoothedResonantMain IntegratedSmoothingIncrement MeasureTheory

def value (η τ t x : ℝ) : ℂ := 1-Complex.exp (-((η:ℂ)+((τ:ℂ)-(t:ℂ)*I)*(x:ℂ)))

theorem radial_identity (η τ t x : ℝ) :
    value η τ t x = 1-(Real.exp (-(η+τ*x)):ℂ)*circle (t*x) := by
  unfold value
  have he : -((η:ℂ)+((τ:ℂ)-(t:ℂ)*I)*(x:ℂ)) =
      ((-(η+τ*x):ℝ):ℂ)+(((t*x:ℝ):ℂ)*I) := by push_cast; ring
  rw [he,Complex.exp_add,circle_eq_exp,Complex.ofReal_exp]

theorem value_ne_zero (η τ t x : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (hx : 0 ≤ x) :
    value η τ t x ≠ 0 := by
  have h := LogKernel.kernel_ne_zero ((η:ℂ)+((τ:ℂ)-(t:ℂ)*I)*(x:ℂ)) 1
    (by simp; positivity) (by norm_num)
  simpa [LogKernel.kernel,value] using h

theorem radial_upper (ρ u M : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hM : 1 ≤ M) (hs : 2*|Real.sin (u/2)| ≤ M) : ‖1-(ρ:ℂ)*circle u‖ ≤ M := by
  have he := radial_distance_sq ρ u
  have ha := sq_abs (Real.sin (u/2))
  have hsq : 4*(Real.sin (u/2))^2 ≤ M^2 := by nlinarith [abs_nonneg (Real.sin (u/2))]
  have hm := mul_le_mul_of_nonneg_left hsq hρ
  have hρsq : ρ^2 ≤ ρ := by nlinarith
  have hlast : ρ*(M^2-1) ≤ M^2-1 := by
    have hM0 : 0 ≤ M^2-1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hρ1 hM0
  nlinarith [norm_nonneg (1-(ρ:ℂ)*circle u)]

theorem sin_one_upper : Real.sin (1:ℝ) ≤ 17/20 := by
  have h := SincBounds.sin_le_quintic 1 (by norm_num)
  norm_num at h
  linarith

theorem sine_upper (u : ℝ) (hu : |u| ≤ 2) : |Real.sin (u/2)| ≤ 17/20 := by
  have hv : |u/2| ≤ 1 := by rw [abs_div]; norm_num; linarith
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_gt_three])]
  apply le_trans _ sin_one_upper
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg (u/2),Real.pi_pos])
    (by linarith [Real.pi_gt_three]) hv

theorem value_upper (η τ t x : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (htx : |t*x| ≤ 2) :
    ‖value η τ t x‖ ≤ 17/10 := by
  rw [radial_identity]
  apply radial_upper _ _ _ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) (by norm_num)
  linarith [sine_upper (t*x) htx]

theorem value_small_upper (η τ t x : ℝ) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (htx : |t*x| ≤ 1) :
    ‖value η τ t x‖ ≤ 1 := by
  rw [radial_identity]
  apply radial_upper _ _ _ (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) le_rfl
  have h := Real.abs_sin_le_abs (x := (t*x)/2)
  rw [abs_div] at h
  norm_num at h
  rw [abs_mul] at htx
  linarith

theorem log_seventeen_tenths : Real.log (17/10:ℝ) ≤ 27/50 := by
  have he : (17/10:ℝ) ≤ Real.exp (27/50) := by
    apply (ExpCertificate.exp_enclosure _ (17/10) 2 12 (by norm_num) (by norm_num) ?_ ?_).1
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr he

end
end Borwein.SmallAnglePole
