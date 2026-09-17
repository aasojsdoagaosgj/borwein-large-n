import Borwein.MiddlePolynomialIntegral
import Borwein.GapIntegralBounds

namespace Borwein.WideGapIntegral
noncomputable section
open Complex MeasureTheory SaddleArcConnection CoefficientArcSplit GapIntegralBounds

theorem gap_order (n : ℕ) (h : ℝ) (hn : 0 < n) (hh0 : 0 ≤ h) (hh1 : h ≤ 6/5) :
    0 ≤ center 0-h/(5*n) ∧
    center 0+h/(5*n) ≤ center 1-h/(5*n) ∧
    center 1+h/(5*n) ≤ center 2-h/(5*n) ∧
    center 2+h/(5*n) ≤ center 3-h/(5*n) ∧
    center 3+h/(5*n) ≤ 2*Real.pi := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hd0 : 0 ≤ h/(5*(n:ℝ)) := by positivity
  have hd : h/(5*(n:ℝ)) ≤ 6/25 := by
    apply (div_le_iff₀ (by positivity : 0 < 5*(n:ℝ))).mpr
    nlinarith
  norm_num [center]
  have hp := Real.pi_gt_three
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem gap_sum_bound (n m : ℕ) (τ h : ℝ) (hn : 0 < n) (hh0 : 0 ≤ h) (hh1 : h ≤ 6/5) :
    ‖gapSum n m τ h‖ ≤ mass n τ h := by
  have hg := gap_order n h hn hh0 hh1
  have h0 := angular_integral_norm (Borwein.polynomial n) m (radius n τ) _ _ hg.1
  have h1 := angular_integral_norm (Borwein.polynomial n) m (radius n τ) _ _ hg.2.1
  have h2 := angular_integral_norm (Borwein.polynomial n) m (radius n τ) _ _ hg.2.2.1
  have h3 := angular_integral_norm (Borwein.polynomial n) m (radius n τ) _ _ hg.2.2.2.1
  have h4 := angular_integral_norm (Borwein.polynomial n) m (radius n τ) _ _ hg.2.2.2.2
  have htri (a b c d e : ℂ) : ‖a+b+c+d+e‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖+‖e‖ := by
    have hab := norm_add_le a b
    have hc := norm_add_le (a+b) c
    have hd := norm_add_le (a+b+c) d
    have he := norm_add_le (a+b+c+d) e
    linarith
  unfold gapSum mass
  exact (htri _ _ _ _ _).trans (add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4)

theorem minor_contribution_bound (n m : ℕ) (τ h : ℝ) (hn : 0 < n) (hh0 : 0 ≤ h) (hh1 : h ≤ 6/5) :
    ‖minorContribution n m τ h‖ ≤ mass n τ h/((radius n τ)^m*(2*Real.pi)) := by
  have hr : 0 < radius n τ := Real.exp_pos _
  unfold minorContribution
  rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le,
    Complex.norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  exact div_le_div_of_nonneg_right (gap_sum_bound n m τ h hn hh0 hh1) (by positivity)

theorem coefficient_error_with_outer_mass (n m : ℕ) (τ N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ (2/5) N+
      MiddlePolynomialIntegral.error n τ+
      mass n τ (6/5)/((radius n τ)^m*(2*Real.pi)*bulkScale n m τ) := by
  have hnNat : 0 < n := by exact_mod_cast hN.trans_le hn
  apply (MiddlePolynomialIntegral.coefficient_error n m τ N hN hn hτ0 hτ1 hs).trans
  apply add_le_add le_rfl
  have hb := div_le_div_of_nonneg_right (minor_contribution_bound n m τ (6/5) hnNat
    (by norm_num) (by norm_num)) (bulkScale_pos n m τ hnNat).le
  simpa only [div_div] using hb

end
end Borwein.WideGapIntegral
