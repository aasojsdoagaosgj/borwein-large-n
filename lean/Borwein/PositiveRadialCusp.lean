import Borwein.IntegratedSmoothingIncrement
import Borwein.DilogarithmUpper
import Borwein.ResonantLimitPolynomial

set_option autoImplicit false

namespace Borwein.PositiveRadialCusp
noncomputable section
open Complex MeasureTheory DilogarithmUpper IntegratedSmoothingIncrement
  RadialSmoothingIncrement SmoothedResonantMain LogKernel

def A : ℝ := Real.pi^2/6
def C : ℝ := 2*Real.pi^2/15
def numerator (τ : ℝ) : ℝ := C-radial τ-(radial τ)^2/A

theorem radial_representation (τ : ℝ) (hτ : 0 < τ) :
    PhaseIntegral.radialR τ = ((radial (5*τ))/5-radial τ+C)/τ := by
  rw [radialR_eq_re_kernelR τ hτ,Dilogarithm.kernelR_eq_dilog _ (by simpa using hτ)]
  have h5 : (5:ℂ)*(τ:ℂ) = ((5*τ:ℝ):ℂ) := by push_cast; ring
  rw [h5,dilog_radial (5*τ) (by positivity),dilog_radial τ hτ.le]
  simp [Complex.div_re,Complex.normSq_apply,C,pow_two,Complex.mul_re]
  field_simp
  ring

theorem radial_lower (τ : ℝ) (hτ : 0 < τ) :
    (C-radial τ)/τ ≤ PhaseIntegral.radialR τ := by
  rw [radial_representation τ hτ]
  apply div_le_div_of_nonneg_right _ hτ.le
  have h := radial_nonneg (5*τ)
  linarith

theorem pole_upper (b : ℕ) (η τ t : ℝ) (hb : 0 < b) (hη : 0 < η) (hτ : 0 < τ) :
    poleIntegral b η ((τ:ℂ)-(t:ℂ)*I) ≤
      (radial ((b:ℝ)*τ))^2/(4*A*((b:ℝ)*τ))+entropy (η/τ) := by
  have h := IntegratedSmoothingIncrement.pole_upper b η ((τ:ℂ)-(t:ℂ)*I)
    hb hη (by simpa using hτ)
  have hh := hIntegral_upper ((b:ℂ)*((τ:ℂ)-(t:ℂ)*I)) (by simp; positivity)
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,Complex.sub_re,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
    sub_zero,sub_self] at h hh
  exact h.trans (add_le_add hh le_rfl)

theorem denominator_one_upper (η τ t : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ (radial τ)^2/(A*τ)+4*entropy (η/τ) := by
  have h := mul_le_mul_of_nonneg_left (pole_upper 1 η τ t (by norm_num) hη hτ)
    (by norm_num : (0:ℝ) ≤ 4)
  norm_num only [Nat.cast_one,one_mul] at h
  exact h.trans_eq (by ring)

theorem denominator_one_gap (η τ t : ℝ) (hη : 0 < η) (hτ : 0 < τ) :
    numerator τ/τ-4*entropy (η/τ) ≤
      PhaseIntegral.radialR τ-4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) := by
  have hR := radial_lower τ hτ
  have hH := denominator_one_upper η τ t hη hτ
  have he : numerator τ/τ = (C-radial τ)/τ-(radial τ)^2/(A*τ) := by
    unfold numerator
    ring
  rw [he]
  linarith

theorem numerator_mono {u τ : ℝ} (hu : 0 ≤ u) (huτ : u ≤ τ) : numerator u ≤ numerator τ := by
  have hB := radial_mono hu huτ
  have hB0 := radial_nonneg τ
  have hsq := sq_le_sq₀ hB0 (radial_nonneg u) |>.mpr hB
  have hA : 0 ≤ A := by unfold A; positivity
  have hd := div_le_div_of_nonneg_right hsq hA
  unfold numerator
  linarith

theorem cell_gap (η u v τ t γ : ℝ) (hη : 0 < η) (hu : 0 < u)
    (huτ : u ≤ τ) (hτv : τ ≤ v) (hnum : 0 ≤ numerator u)
    (hcell : γ ≤ numerator u/v-4*entropy (η/u)) :
    γ ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) := by
  have hτ := hu.trans_le huτ
  have hb := numerator_mono hu.le huτ
  have hd := div_le_div_of_nonneg_left hnum hτ hτv
  have he := entropy_mono (div_pos hη hτ)
    (div_le_div_of_nonneg_left hη.le hu huτ)
  have hh := div_le_div_of_nonneg_right hb hτ.le
  have hg := denominator_one_gap η τ t hη hτ
  linarith

end
end Borwein.PositiveRadialCusp
