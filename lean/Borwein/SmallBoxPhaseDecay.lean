import Borwein.CentralMoments
import Borwein.SincBounds
import Borwein.PhaseSingular

namespace Borwein.SmallBoxPhaseDecay
noncomputable section
open scoped BigOperators
open Complex PhaseGap RadialMoments RadialDerivatives PhaseIntegral

def pairVariance (p : Fin 5 → ℝ) : ℝ :=
  (p 0*p 1+p 1*p 2+p 2*p 3+p 3*p 4) +
  4*(p 0*p 2+p 1*p 3+p 2*p 4) +
  9*(p 0*p 3+p 1*p 4)+16*(p 0*p 4)

theorem pair_variance_identity (p : Fin 5 → ℝ) :
    pairVariance p = (∑ j : Fin 5, p j)*(∑ j : Fin 5, (j:ℝ)^2*p j)-
      (∑ j : Fin 5, (j:ℝ)*p j)^2 := by
  norm_num [pairVariance,Fin.sum_univ_five]
  ring

theorem radial_pair_variance (y : ℝ) : pairVariance (radialWeight y) = variance y := by
  rw [pair_variance_identity,radialWeight_sum,← second_eq_weighted,← mean_eq_weighted]
  simp [variance]

theorem cosine_gap_lower (u : ℝ) (hu : |u| ≤ 8/5) :
    (39/100:ℝ)*u^2 ≤ 1-Real.cos u := by
  have hc := SincBounds.cos_le_quartic |u| (abs_nonneg u)
  rw [Real.cos_abs,sq_abs,show |u|^4=(u^2)^2 by rw [show 4=2*2 by decide,pow_mul,sq_abs]] at hc
  have hs := pow_le_pow_left₀ (abs_nonneg u) hu 2
  rw [sq_abs] at hs
  have h4 := mul_le_mul_of_nonneg_left hs (sq_nonneg u)
  nlinarith [sq_nonneg u]

theorem grouped_gap_lower (p : Fin 5 → ℝ) (hp : ∀ j, 0 ≤ p j)
    (t : ℝ) (ht : |t| ≤ 2/5) :
    (39/100:ℝ)*t^2*pairVariance p ≤ groupedGap p t := by
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hp4 := hp 4
  have hc (d : ℝ) (hd : 0 ≤ d) (hd4 : d ≤ 4) :
      (39/100:ℝ)*(d*t)^2 ≤ 1-Real.cos (d*t) := by
    apply cosine_gap_lower
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

theorem gap_density_lower (τ t x : ℝ) (ht : |t| ≤ 2/5) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    (39/100:ℝ)*t^2*secondDensity τ x ≤ gapDensity τ t x := by
  have htx : |t*x| ≤ 2/5 := by
    rw [abs_mul,abs_of_nonneg hx.1]
    nlinarith [abs_nonneg t,hx.2]
  have h := grouped_gap_lower (radialWeight (τ*x)) (fun j => (radialWeight_pos _ j).le) (t*x) htx
  rw [radial_pair_variance] at h
  simpa only [gapDensity,secondDensity,mul_pow,mul_assoc,mul_comm,mul_left_comm] using h

theorem radial_real_decay (τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    (complexR ((τ:ℂ)-(t:ℂ)*I)).re-radialR τ ≤
      -(39/100:ℝ)*secondDerivative τ*t^2 := by
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0:ℝ) ≤ 1)
    (((continuous_secondDensity τ).const_mul ((39/100:ℝ)*t^2)).intervalIntegrable 0 1)
    ((continuous_gapDensity τ t).intervalIntegrable 0 1)
    (fun x hx => gap_density_lower τ t x ht hx)
  rw [intervalIntegral.integral_const_mul] at hi
  have hq := ResonantCertificate.gap_integral_le_quadratic τ t
  have hl := PhaseSingular.integral_phase_gap_nonneg τ t hτ
  rw [PhaseSingular.integral_phase_R_nonneg τ t hτ] at hl
  change (39/100:ℝ)*t^2*secondDerivative τ ≤ _ at hi
  nlinarith

theorem complexR_real (τ : ℝ) : complexR (τ:ℂ) = (radialR τ:ℂ) := by
  unfold complexR radialR
  rw [← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← Complex.ofReal_mul,fiveSum_real]
  exact (Complex.ofReal_log (radialDenominator_pos (τ*x)).le).symm

def saddlePhase (n τ t : ℝ) : ℂ :=
  (n:ℂ)*(complexR ((τ:ℂ)-(t:ℂ)*I)-complexR (τ:ℂ)+
    (firstDerivative τ:ℂ)*(t:ℂ)*I)

theorem saddle_phase_decay (n τ t : ℝ) (hn : 0 ≤ n) (hτ : 0 ≤ τ)
    (ht : |t| ≤ 2/5) :
    (saddlePhase n τ t).re ≤ -(39/100:ℝ)*n*secondDerivative τ*t^2 := by
  have h := mul_le_mul_of_nonneg_left (radial_real_decay τ t hτ ht) hn
  unfold saddlePhase
  rw [complexR_real]
  simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.sub_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  nlinarith

end
end Borwein.SmallBoxPhaseDecay
