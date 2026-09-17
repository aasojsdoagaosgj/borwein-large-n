import Borwein.CertifiedBulkRemainder

set_option autoImplicit false

namespace Borwein.BulkSignCriterion
noncomputable section
open RadialDerivatives SaddleArcConnection CombinedAmplitude CertifiedBulkRemainder

theorem mainBudget_nonneg (ζ : ℂ) (a : ℕ) (τ : ℝ) : 0 ≤ mainBudget ζ a τ := by
  have he := GaussianNormalization.coefficient_nonneg ζ a τ
  have ht := EMUniformBounds.thetaBudget_nonneg ζ a τ (2/5) (by norm_num)
  unfold mainBudget
  positivity

theorem real_coefficient_error (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    |((Borwein.polynomial n).coeff m:ℝ)/bulkScale n m τ-
      (psi FivePoleCircle.zeta (m%5) (τ:ℂ)).re| ≤
      mainBudget FivePoleCircle.zeta (m%5) τ/31147+(9/100000:ℝ) := by
  have h := CertifiedBulkRemainder.coefficient_error n m τ hn hτ hT hs
  have hr := (Complex.abs_re_le_norm
    (((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      psi FivePoleCircle.zeta (m%5) (τ:ℂ))).trans h
  have hid : (((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)) =
      (((((Borwein.polynomial n).coeff m:ℝ)/bulkScale n m τ):ℝ):ℂ) := by push_cast; rfl
  rw [hid] at hr
  simp only [Complex.sub_re,Complex.ofReal_re] at hr
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hb := div_le_div_of_nonneg_left (mainBudget_nonneg FivePoleCircle.zeta (m%5) τ)
    (by norm_num : (0:ℝ) < 31147) hn'
  linarith

/-- A certified real-part margin at the fixed threshold suffices for every larger n.
The sign is supplied as +1 or -1; this theorem does not assume a phase-sign table. -/
theorem signed_coefficient (n m : ℕ) (τ s : ℝ) (hn : 31147 ≤ n)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2))
    (hsign : s = 1 ∨ s = -1)
    (hmargin : mainBudget FivePoleCircle.zeta (m%5) τ/31147+(9/100000:ℝ) <
      s*(psi FivePoleCircle.zeta (m%5) (τ:ℂ)).re) :
    0 < s*((Borwein.polynomial n).coeff m:ℝ) := by
  have herr := abs_le.mp (real_coefficient_error n m τ hn hτ hT hs)
  have hn0 : 0 < n := by omega
  have hb := bulkScale_pos n m τ hn0
  rcases hsign with rfl | rfl
  · have hc : 0 < ((Borwein.polynomial n).coeff m:ℝ)/bulkScale n m τ := by linarith [herr.1]
    have hcp := (div_pos_iff.mp hc).resolve_right (by intro h; linarith [h.2])
    simpa only [one_mul] using hcp.1
  · have hc : ((Borwein.polynomial n).coeff m:ℝ)/bulkScale n m τ < 0 := by linarith [herr.2]
    have hcp : ((Borwein.polynomial n).coeff m:ℝ) < 0 := by
      exact (div_neg_iff.mp hc).resolve_left (by intro h; linarith [h.2]) |>.1
    linarith

end
end Borwein.BulkSignCriterion
