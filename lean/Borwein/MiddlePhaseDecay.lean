import Borwein.SmallBoxPhaseDecay
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Borwein.MiddlePhaseDecay
noncomputable section
open Complex Set PhaseGap RadialMoments RadialDerivatives PhaseIntegral SmallBoxPhaseDecay

def curvature (v : ℝ) : ℝ := (Real.sin (2*v)/(2*v))^2/2

theorem sine_chord (b x : ℝ) (hb : 0 < b) (hbp : b ≤ Real.pi) (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    Real.sin b/b*x ≤ Real.sin x := by
  have hratio : x/b ≤ 1 := (div_le_one hb).mpr hxb
  have he := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0:ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl,Real.pi_pos.le⟩)
    (show b ∈ Icc 0 Real.pi from ⟨hb.le,hbp⟩)
    (sub_nonneg.mpr hratio) (div_nonneg hx0 hb.le) (by ring : 1-x/b+x/b=1)
  simp only [smul_eq_mul,Real.sin_zero,mul_zero,zero_add] at he
  rw [div_mul_cancel₀ x hb.ne'] at he
  convert! he using 1
  ring

theorem cosine_gap_lower (v u : ℝ) (hv : 0 < v) (hvp : 2*v ≤ Real.pi) (hu : |u| ≤ 4*v) :
    curvature v*u^2 ≤ 1-Real.cos u := by
  have hb : 0 < 2*v := by positivity
  have hx0 : 0 ≤ |u|/2 := by positivity
  have hxb : |u|/2 ≤ 2*v := by linarith
  have hs := sine_chord (2*v) (|u|/2) hb hvp hx0 hxb
  have hsin := Real.sin_nonneg_of_mem_Icc (show 2*v ∈ Icc (0:ℝ) Real.pi from ⟨hb.le,hvp⟩)
  have hsq := pow_le_pow_left₀ (mul_nonneg (div_nonneg hsin hb.le) hx0) hs 2
  have hc := Real.cos_two_mul_eq_one_sub (|u|/2)
  rw [show 2*(|u|/2)=|u| by ring,Real.cos_abs] at hc
  have he : (Real.sin (2*v)/(2*v)*(|u|/2))^2 = curvature v*u^2/2 := by
    unfold curvature
    simp only [mul_pow,div_pow,sq_abs]
    ring
  rw [he] at hsq
  linarith

theorem grouped_gap_lower (p : Fin 5 → ℝ) (hp : ∀ j, 0 ≤ p j) (v t : ℝ)
    (hv : 0 < v) (hvp : 2*v ≤ Real.pi) (ht : |t| ≤ v) :
    curvature v*t^2*pairVariance p ≤ groupedGap p t := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  have hc (d : ℝ) (hd : 0 ≤ d) (hd4 : d ≤ 4) :
      curvature v*(d*t)^2 ≤ 1-Real.cos (d*t) := by
    apply cosine_gap_lower v _ hv hvp
    rw [abs_mul,abs_of_nonneg hd]
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left (hc 1 (by norm_num) (by norm_num))
    (show 0 ≤ p 0*p 1+p 1*p 2+p 2*p 3+p 3*p 4 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hc 2 (by norm_num) (by norm_num))
    (show 0 ≤ p 0*p 2+p 1*p 3+p 2*p 4 by positivity)
  have h3 := mul_le_mul_of_nonneg_left (hc 3 (by norm_num) (by norm_num))
    (show 0 ≤ p 0*p 3+p 1*p 4 by positivity)
  have h4 := mul_le_mul_of_nonneg_left (hc 4 (by norm_num) (by norm_num))
    (show 0 ≤ p 0*p 4 by positivity)
  simp only [one_mul] at h1
  unfold pairVariance groupedGap
  nlinarith

theorem gap_density_lower (τ v t x : ℝ) (hv : 0 < v) (hvp : 2*v ≤ Real.pi)
    (ht : |t| ≤ v) (hx : x ∈ Icc (0:ℝ) 1) :
    curvature v*t^2*secondDensity τ x ≤ gapDensity τ t x := by
  have htx : |t*x| ≤ v := by
    rw [abs_mul,abs_of_nonneg hx.1]
    nlinarith [abs_nonneg t,hx.2]
  have hb := grouped_gap_lower (radialWeight (τ*x)) (fun j => (radialWeight_pos _ j).le) v (t*x) hv hvp htx
  rw [radial_pair_variance] at hb
  simpa only [gapDensity,secondDensity,mul_pow,mul_assoc,mul_comm,mul_left_comm] using hb

theorem radial_real_decay (τ v t : ℝ) (hτ : 0 ≤ τ) (hv : 0 < v) (hvp : 2*v ≤ Real.pi) (ht : |t| ≤ v) :
    (complexR ((τ:ℂ)-(t:ℂ)*I)).re-radialR τ ≤ -curvature v*secondDerivative τ*t^2 := by
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0:ℝ) ≤ 1)
    (((continuous_secondDensity τ).const_mul (curvature v*t^2)).intervalIntegrable 0 1)
    ((continuous_gapDensity τ t).intervalIntegrable 0 1)
    (fun x hx => gap_density_lower τ v t x hv hvp ht hx)
  rw [intervalIntegral.integral_const_mul] at hi
  have hq := ResonantCertificate.gap_integral_le_quadratic τ t
  have hl := PhaseSingular.integral_phase_gap_nonneg τ t hτ
  rw [PhaseSingular.integral_phase_R_nonneg τ t hτ] at hl
  change curvature v*t^2*secondDerivative τ ≤ _ at hi
  nlinarith

end
end Borwein.MiddlePhaseDecay
