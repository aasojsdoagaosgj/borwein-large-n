import Borwein.MiddlePolynomialBounds
import Borwein.CoefficientArcSplit

namespace Borwein.MiddlePolynomialIntegral
noncomputable section
open Complex Set MeasureTheory RadialDerivatives GaussianNormalization SaddleArcConnection
  FivePoleCircle CombinedAmplitude

def error (n : ℕ) (τ : ℝ) : ℝ :=
  (192/5:ℝ)*Real.sqrt ((n:ℝ)*secondDerivative τ/(2*Real.pi))*
    Real.exp (-(13/250:ℝ)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ))

def middleContribution (n m : ℕ) (τ : ℝ) : ℂ :=
  majorContribution n m τ (6/5)-majorContribution n m τ (2/5)

theorem band_integral_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ)
    (τ u v : ℝ) (hn : 0 < n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (huv : u ≤ v)
    (hband : ∀ t ∈ Icc u v, 2/5 ≤ |t| ∧ |t| ≤ 6/5) :
    ‖∫ t in u..v, FiniteMajorArc.integrand ζ a n τ t‖ ≤
      (v-u)*24*Real.exp (-(13/250:ℝ)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ)) := by
  have hb := MiddlePhaseIntegral.bounded_norm_integral (FiniteMajorArc.integrand ζ a n τ) u v
    (24*Real.exp (-(13/250:ℝ)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ))) huv (by
      intro t ht
      exact MiddlePolynomialBounds.integrand_middle_bound ζ hζ a n τ t hn hτ0 hτ1
        (hband t ht).1 (hband t ht).2)
  simpa only [mul_assoc] using hb

theorem two_sided_integral_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ)
    (τ : ℝ) (hn : 0 < n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) :
    ‖(∫ t in (-6/5:ℝ)..-2/5, FiniteMajorArc.integrand ζ a n τ t)+
      (∫ t in (2/5:ℝ)..6/5, FiniteMajorArc.integrand ζ a n τ t)‖ ≤
      (192/5:ℝ)*Real.exp (-(13/250:ℝ)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ)) := by
  have hl := band_integral_bound ζ hζ a n τ (-6/5) (-2/5) hn hτ0 hτ1 (by norm_num) (by
    intro t ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    constructor <;> linarith [ht.1,ht.2])
  have hr := band_integral_bound ζ hζ a n τ (2/5) (6/5) hn hτ0 hτ1 (by norm_num) (by
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    exact ht)
  have hb := (norm_add_le _ _).trans (add_le_add hl hr)
  convert! hb using 1
  ring

theorem normalized_two_sided_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ)
    (τ : ℝ) (hn : 0 < n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) :
    ‖(∫ t in (-6/5:ℝ)..-2/5, FiniteMajorArc.integrand ζ a n τ t)+
      (∫ t in (2/5:ℝ)..6/5, FiniteMajorArc.integrand ζ a n τ t)‖/scale n τ ≤ error n τ := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : (scale n τ)⁻¹ = Real.sqrt ((n:ℝ)*secondDerivative τ/(2*Real.pi)) := by
    unfold scale
    rw [← Real.sqrt_inv]
    congr 1
    simp
  have hb := div_le_div_of_nonneg_right (two_sided_integral_bound ζ hζ a n τ hn hτ0 hτ1)
    (scale_pos n τ hn0).le
  unfold error
  convert! hb using 1
  simp only [div_eq_mul_inv,hs]
  ring

theorem annulus_identity (f : ℝ → ℂ) (hf : Continuous f) :
    (∫ t in (-6/5:ℝ)..6/5, f t)-(∫ t in (-2/5:ℝ)..2/5, f t) =
      (∫ t in (-6/5:ℝ)..-2/5, f t)+(∫ t in (2/5:ℝ)..6/5, f t) := by
  rw [CoefficientArcSplit.interval_difference f hf (-6/5) (6/5),
    CoefficientArcSplit.interval_difference f hf (-2/5) (2/5),
    CoefficientArcSplit.interval_difference f hf (-6/5) (-2/5),
    CoefficientArcSplit.interval_difference f hf (2/5) (6/5)]
  ring

theorem normalized_middle_identity (n m : ℕ) (τ : ℝ) (hn : 0 < n)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    middleContribution n m τ/(bulkScale n m τ:ℂ) =
      ((∫ t in (-6/5:ℝ)..-2/5, FiniteMajorArc.integrand zeta (m%5) n τ t)+
       (∫ t in (2/5:ℝ)..6/5, FiniteMajorArc.integrand zeta (m%5) n τ t))/(scale n τ:ℂ) := by
  rw [middleContribution,sub_div,normalized_contribution n m τ (6/5) hn hs,
    normalized_contribution n m τ (2/5) hn hs,← sub_div]
  congr 1
  simpa only [neg_div] using annulus_identity _ (FiniteMajorArc.integrand_continuous zeta (m%5) n τ)

theorem middle_contribution_bound (n m : ℕ) (τ : ℝ) (hn : 0 < n)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖middleContribution n m τ‖/bulkScale n m τ ≤ error n τ := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have he := congrArg norm (normalized_middle_identity n m τ hn hs)
  rw [norm_div,norm_div,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (bulkScale_pos n m τ hn).le,
    Real.norm_of_nonneg (scale_pos n τ hn0).le] at he
  rw [he]
  exact normalized_two_sided_bound zeta zeta_primitive (m%5) n τ hn hτ0 hτ1

theorem coefficient_split (n m : ℕ) (τ : ℝ) :
    (((Borwein.polynomial n).coeff m:ℤ):ℂ) =
      majorContribution n m τ (2/5)+middleContribution n m τ+
        CoefficientArcSplit.minorContribution n m τ (6/5) := by
  rw [CoefficientArcSplit.coefficient_split n m τ (6/5)]
  unfold middleContribution
  ring

theorem coefficient_error (n m : ℕ) (τ N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖(((Borwein.polynomial n).coeff m:ℤ):ℂ)/(bulkScale n m τ:ℂ)-psi zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError zeta (m%5) n τ (2/5) N+error n τ+
        ‖CoefficientArcSplit.minorContribution n m τ (6/5)‖/bulkScale n m τ := by
  have hn0 : 0 < (n:ℝ) := hN.trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hb := major_contribution_error n m τ (2/5) N hN hn hτ0 hτ1 (by norm_num) (by norm_num) hs
  have hm := middle_contribution_bound n m τ hnNat hτ0 hτ1 hs
  rw [coefficient_split]
  have he (A B C P ψ : ℂ) : (A+B+C)/P-ψ = (A/P-ψ)+B/P+C/P := by ring
  rw [he]
  have ht (A B C : ℂ) : ‖A+B+C‖ ≤ ‖A‖+‖B‖+‖C‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  apply (ht _ _ _).trans
  rw [norm_div,norm_div,Complex.norm_real,Real.norm_of_nonneg (bulkScale_pos n m τ hnNat).le]
  exact add_le_add (add_le_add hb hm) le_rfl

end
end Borwein.MiddlePolynomialIntegral
