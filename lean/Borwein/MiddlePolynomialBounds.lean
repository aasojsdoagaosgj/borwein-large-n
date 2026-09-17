import Borwein.LargeBoxAmplitude
import Borwein.MiddlePhaseIntegral
import Borwein.FiniteMajorArc

namespace Borwein.MiddlePolynomialBounds
noncomputable section
open Complex Set MeasureTheory FiveRootProductExpansion MainTermIdentification LargeBoxEulerMaclaurin
  PhaseIntegral RadialDerivatives CombinedAmplitude

theorem polynomial_norm_bound (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (n : ℕ) (hn : 0 < n)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 6/5) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ z n) (Borwein.polynomial n)‖ ≤
      6*Real.exp ((n:ℝ)*(complexR z).re+7200/(n:ℝ)) := by
  have he := large_box_expansion ξ z hξ n hn hz0 hz1 hi
  have ha := (LargeBoxAmplitude.amplitude_norm_lt_six ξ z hξ hz0 hi).le
  have hr := (Complex.re_le_norm (largeRemainder ξ z n)).trans he.2
  rw [he.1,norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp]
  have hre : ((n:ℂ)*FifthRootLogarithm.rootIntegral ξ z).re = (n:ℝ)*(complexR z).re := by
    simp [LargeBoxMainIntegral.rootIntegral_real_part ξ z hξ hz0 hi]
  rw [hre]
  have hb := mul_le_mul (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le)
    (Real.exp_le_exp.mpr hr) (Real.exp_pos _).le (by positivity : (0:ℝ) ≤ Real.exp ((n:ℝ)*(complexR z).re)*6)
  convert! hb using 1
  rw [Real.exp_add]
  ring

theorem polynomial_middle_bound (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (n : ℕ) (τ t : ℝ) (hn : 0 < n)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (ht0 : 2/5 ≤ |t|) (ht1 : |t| ≤ 6/5) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point ξ ((τ:ℂ)-(t:ℂ)*I) n) (Borwein.polynomial n)‖ ≤
      6*Real.exp ((n:ℝ)*(radialR τ-(13/250:ℝ)*secondDerivative τ)+7200/(n:ℝ)) := by
  have hn0 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  have hb := polynomial_norm_bound ξ ((τ:ℂ)-(t:ℂ)*I) hξ n hn
    (by simpa using hτ0) (by simpa using hτ1) (by simpa using ht1)
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 6)
  apply Real.exp_le_exp.mpr
  have hd := mul_le_mul_of_nonneg_left (MiddlePhaseCertificate.band_real_decay τ t hτ0 ht0 ht1) hn0
  nlinarith

theorem integrand_middle_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ t : ℝ) (hn : 0 < n)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (ht0 : 2/5 ≤ |t|) (ht1 : |t| ≤ 6/5) :
    ‖FiniteMajorArc.integrand ζ a n τ t‖ ≤
      24*Real.exp (-(13/250:ℝ)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ)) := by
  have hs := weighted_sum_bound ζ hζ a
    (fun j => Polynomial.eval₂ (Int.castRingHom ℂ) (point (coefficients ζ j) ((τ:ℂ)-(t:ℂ)*I) n) (Borwein.polynomial n))
    (6*Real.exp ((n:ℝ)*(radialR τ-(13/250:ℝ)*secondDerivative τ)+7200/(n:ℝ)))
    (fun j => polynomial_middle_bound _ (coefficient_primitive ζ hζ j) n τ t hn hτ0 hτ1 ht0 ht1)
  unfold FiniteMajorArc.integrand
  rw [norm_mul,Complex.norm_exp,SmallBoxPhaseDecay.complexR_real]
  simp only [Complex.mul_re,Complex.add_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_im,Complex.I_re,Complex.I_im,Complex.natCast_re,Complex.natCast_im,
    mul_zero,zero_mul,mul_one,sub_zero,add_zero]
  have hb := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-(n:ℝ)*radialR τ)).le
  apply le_trans (by convert! hb using 1 <;> ring)
  rw [show Real.exp (-(n:ℝ)*radialR τ)*(4*(6*Real.exp ((n:ℝ)*(radialR τ-(13/250:ℝ)*secondDerivative τ)+7200/(n:ℝ)))) =
      24*(Real.exp (-(n:ℝ)*radialR τ)*Real.exp ((n:ℝ)*(radialR τ-(13/250:ℝ)*secondDerivative τ)+7200/(n:ℝ))) by ring,
    ← Real.exp_add]
  apply le_of_eq
  congr 2
  ring

end
end Borwein.MiddlePolynomialBounds
