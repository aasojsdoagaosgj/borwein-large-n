import Borwein.ResonantFourierSplit

set_option autoImplicit false

namespace Borwein.ResonantPolynomialBound
noncomputable section
open Complex FiniteBlockLocalization ZeroPoleBudget ResonantFourierSplit ResonantArgumentBounds
  ExponentialKernelRemainder

theorem coefficient_weight (n k : ℕ) (z : ℂ) (η : ℝ) :
    FiniteFourierKernel.coefficient n k z (Real.exp (-η)) =
      (weight η k:ℂ)*FiniteFourierKernel.finiteSum n (z^k) := by
  unfold FiniteFourierKernel.coefficient
  rw [← Complex.ofReal_pow,← Complex.ofReal_natCast,← Complex.ofReal_div,weight_eq]

theorem range_full (n K : ℕ) (z : ℂ) (η : ℝ) :
    (∑ k ∈ Finset.range (K+1), FiniteFourierKernel.coefficient n k z (Real.exp (-η))) =
      full n K z η := by
  rw [sum_range_eq_Icc]
  simp only [coefficient_weight,full]

theorem full_approximation (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) :
    ‖full n K (point n τ θ) η-main n K τ θ η q‖ ≤
      ‖nonresonant n K (point n τ θ) η q‖+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have he := approximation_error n N Q K τ T θ η q hN hn hQ hτ hT hη hη1 hq hZ
  have hb := (div_le_div_iff_of_pos_right hn0).mp he
  rw [full_error_identity]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hb)

theorem polynomial_log_upper (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi)
    (hv : Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n) ≠ 0) :
    Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      2*η*n-(main n K τ θ η q).re+‖nonresonant n K (point n τ θ) η q‖+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η)+tail n K η := by
  have hp := FiniteFourierKernel.polynomial_log_truncated_upper n K (point n τ θ)
    (point_norm_le n τ θ hτ) η hη hv
  rw [range_full] at hp
  have hb := full_approximation n N Q K τ T θ η q hN hn hQ hτ hT hη hη1 hq hZ
  have hr := Complex.re_le_norm (-(full n K (point n τ θ) η-main n K τ θ η q))
  rw [Complex.neg_re,Complex.sub_re,norm_neg] at hr
  unfold tail
  linarith

theorem polynomial_norm_upper (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (2*η*n-(main n K τ θ η q).re+‖nonresonant n K (point n τ θ) η q‖+
        4*kappa (radiusBound N Q K T q)*Real.log (2/η)+tail n K η) := by
  by_cases hv : Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n) = 0
  · rw [hv,norm_zero]
    positivity
  have h := Real.exp_le_exp.mpr (polynomial_log_upper n N Q K τ T θ η q
    hN hn hQ hτ hT hη hη1 hq hZ hv)
  rwa [Real.exp_log (norm_pos_iff.mpr hv)] at h

end
end Borwein.ResonantPolynomialBound
