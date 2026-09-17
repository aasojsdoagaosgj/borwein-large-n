import Borwein.EndpointSaddleEnergy
import Borwein.AbsoluteGaussianMoment

set_option autoImplicit false

namespace Borwein.EndpointGaussianIntegral
noncomputable section
open Complex MeasureTheory Set EndpointActualPhase EndpointTaylor EndpointPhaseDecay EndpointSaddleIdentification

def width (v : ℝ) : ℝ := 3*v/4
def variance (n : ℕ) (v : ℝ) : ℝ := (f2 n v 0).re
def normalizer (n : ℕ) (v : ℝ) : ℝ := Real.sqrt (2*Real.pi/variance n v)
def localIntegral (n : ℕ) (v : ℝ) : ℂ := ∫ y in -(width v)..width v, exp (phase n v y)

theorem phase_continuous (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : Continuous (phase n v) := by
  have hf : Continuous (f0 n v) := continuous_iff_continuousAt.mpr (fun y => (f0_deriv n v y hn hv).continuousAt)
  exact (hf.sub continuous_const).sub (by fun_prop)

theorem gaussian_continuous (n : ℕ) (v : ℝ) : Continuous (EndpointPhaseDecay.gaussian n v) := by
  unfold EndpointPhaseDecay.gaussian
  fun_prop

theorem local_difference_bound (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖localIntegral n v-(∫ y in -(width v)..width v, exp (EndpointPhaseDecay.gaussian n v y))‖ ≤
      (1280000/28227:ℝ)*v^2 := by
  let c : ℝ := (97/1000)/v^3
  let D : ℝ := (64/25)/(6*v^4)
  have hc : 0 < c := by dsimp [c]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hw : 0 ≤ width v := by unfold width; positivity
  have hP := (phase_continuous n v hn hv).cexp
  have hG := (gaussian_continuous n v).cexp
  have hB : Continuous (fun y => D*AbsoluteGaussianMoment.integrand c y) := by
    unfold AbsoluteGaussianMoment.integrand
    fun_prop
  rw [localIntegral, ← intervalIntegral.integral_sub (hP.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  calc
    _ ≤ ∫ y in -(width v)..width v, ‖exp (phase n v y)-exp (EndpointPhaseDecay.gaussian n v y)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ y in -(width v)..width v, D*AbsoluteGaussianMoment.integrand c y := by
      apply intervalIntegral.integral_mono_on (by linarith)
        ((hP.sub hG).norm.intervalIntegrable _ _) (hB.intervalIntegrable _ _)
      intro y hy
      have hyb : |y| ≤ 3*v/4 := abs_le.mpr ⟨hy.1, hy.2⟩
      apply (exponential_remainder n v y hn hv hτ hyb).trans_eq
      unfold AbsoluteGaussianMoment.integrand
      dsimp [D, c]
      rw [show -(97/1000:ℝ)*(y^2/v^3)=-(97/1000/v^3)*y^2 by ring]
      ring
    _ ≤ D*(1/c^2) := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (AbsoluteGaussianMoment.absolute_cubic_bound c (width v) hc hw) hD
    _ = _ := by dsimp [D, c]; field_simp; ring

theorem normalizer_pos (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : 0 < normalizer n v := by
  have hV : 0 < variance n v := quadratic_positive n v hn hv
  unfold normalizer
  positivity

theorem gaussian_real_exp (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    exp (EndpointPhaseDecay.gaussian n v y)=(GaussianMoments.gaussian (variance n v/2) y:ℂ) := by
  have he : f2 n v 0=(variance n v:ℂ) := by
    apply Complex.ext
    · rfl
    · rw [quadratic_real n v hn hv, Complex.ofReal_im]
  rw [EndpointPhaseDecay.gaussian, he]
  unfold GaussianMoments.gaussian
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem gaussian_integral_tail (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    ‖(∫ y in -(width v)..width v, exp (EndpointPhaseDecay.gaussian n v y))-(normalizer n v:ℂ)‖ ≤
      normalizer n v*Real.exp (-(variance n v/2)*(width v)^2) := by
  have hV : 0 < variance n v := quadratic_positive n v hn hv
  have he : Real.sqrt (Real.pi/(variance n v/2))=normalizer n v := by
    unfold normalizer
    congr 1
    ring
  have hh := GaussianTail.interval_tail_bound (variance n v/2) (width v) (by positivity) (by unfold width; positivity)
  rw [he] at hh
  simp_rw [gaussian_real_exp n v _ hn hv]
  rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact hh

theorem full_gaussian_bound (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖localIntegral n v-(normalizer n v:ℂ)‖ ≤ (1280000/28227:ℝ)*v^2+
      normalizer n v*Real.exp (-(variance n v/2)*(width v)^2) := by
  have hh := norm_sub_le_norm_sub_add_norm_sub (localIntegral n v)
    (∫ y in -(width v)..width v, exp (EndpointPhaseDecay.gaussian n v y)) (normalizer n v:ℂ)
  exact hh.trans (add_le_add (local_difference_bound n v hn hv hτ) (gaussian_integral_tail n v hn hv))

theorem normalized_gaussian_bound (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖localIntegral n v/(normalizer n v:ℂ)-1‖ ≤ (1280000/28227:ℝ)*v^2/normalizer n v+
      Real.exp (-(variance n v/2)*(width v)^2) := by
  have hJ := normalizer_pos n v hn hv
  have hj0 : (normalizer n v:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hJ
  have he : localIntegral n v/(normalizer n v:ℂ)-1=
      (localIntegral n v-(normalizer n v:ℂ))/(normalizer n v:ℂ) := by field_simp
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hJ]
  apply (div_le_div_of_nonneg_right (full_gaussian_bound n v hn hv hτ) hJ.le).trans_eq
  field_simp

theorem energy_integral (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    (∫ y in -(width v)..width v, exp (EndpointSaddleEnergy.energy n k v y-
      EndpointSaddleEnergy.energy n k v 0))=localIntegral n v := by
  unfold localIntegral
  apply intervalIntegral.integral_congr
  intro y _
  exact congrArg Complex.exp (EndpointSaddleEnergy.energy_difference n k v y hn hv hs)

theorem energy_normalized_bound (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2))
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖(∫ y in -(width v)..width v, exp (EndpointSaddleEnergy.energy n k v y-
      EndpointSaddleEnergy.energy n k v 0))/(normalizer n v:ℂ)-1‖ ≤
      (1280000/28227:ℝ)*v^2/normalizer n v+Real.exp (-(variance n v/2)*(width v)^2) := by
  rw [energy_integral n k v hn hv hs]
  exact normalized_gaussian_bound n v hn hv hτ

end
end Borwein.EndpointGaussianIntegral
