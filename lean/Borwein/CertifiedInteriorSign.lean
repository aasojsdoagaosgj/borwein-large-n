import Borwein.BulkCertificateCast
import Borwein.SaddlePoint

set_option autoImplicit false

namespace Borwein.CertifiedInteriorSign
noncomputable section
open CertifiedBulkMoments CertifiedPhaseLower CertifiedMomentTable BulkCertificateCast
open SignedMainBudget ExplicitPhaseProfile CombinedPhaseSign

theorem budgets (i : Fin 32) (τ : ℝ) (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) :
    relativeBudget τ ≤ R i ∧ absoluteBudget τ ≤ B i := by
  have hτ : 0 ≤ τ := (show 0 ≤ tauLo i by unfold tauLo; positivity).trans hL
  have hm := actual_bounds i τ hL hU
  have hq := (q_bounds i τ hL hU).2
  have hz := RationalMainBudget.radius_upper τ (tauHi i) hτ hU
  have hc := BulkCertificateCast.checks i
  exact ⟨(RationalMainBudget.relative_upper τ _ _ _ _ (v_positive i) hm.1 hm.2.1 hm.2.2 hz).trans hc.2.2.1,
    (RationalMainBudget.absolute_upper τ _ _ _ _ (v_positive i) hm.1 hm.2.1 hq hz).trans hc.2.2.2.1⟩

theorem phase_lower (a : ℕ) (ha : a < 5) (i : Fin 32) (τ : ℝ)
    (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) : P i ≤ sign a*phase a τ := by
  exact ((BulkCertificateCast.checks i).2.2.2.2.1).trans
    ((bound_three_le a i).trans (CertifiedPhaseLower.signed_phase a ha i τ hL hU))

theorem coefficient_sign (n m : ℕ) (τ : ℝ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    0 < sign (m%5)*((Borwein.polynomial n).coeff m:ℝ) := by
  obtain ⟨i,hi⟩ := cell_cover τ hτ hT
  have hc := BulkCertificateCast.checks i
  have hb := budgets i τ hi.1 hi.2
  exact signed_coefficient_from_certificate n m τ (P i) (R i) (B i) hn hτ hT hs
    hc.1 (phase_lower (m%5) (Nat.mod_lt _ (by norm_num)) i τ hi.1 hi.2)
    hb.1 hb.2 hc.2.1 hc.2.2.2.2.2

theorem saddle_in_closed_interval (r : ℝ)
    (hL : -RadialDerivatives.firstDerivative (11/2) ≤ r) (hU : r ≤ 1) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ 11/2 ∧ -RadialDerivatives.firstDerivative τ = r := by
  have hiv := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 11/2)
    SaddlePoint.continuous_firstDerivative.continuousOn
  obtain ⟨τ,hτ,he⟩ := hiv (show -r ∈ Set.Icc (RadialDerivatives.firstDerivative 0)
      (RadialDerivatives.firstDerivative (11/2)) from by
    rw [RadialDerivatives.firstDerivative_zero]
    constructor <;> linarith)
  exact ⟨τ,hτ.1,hτ.2,by linarith⟩

theorem coefficient_sign_of_ratio (n m : ℕ) (hn : 31147 ≤ n)
    (hL : -RadialDerivatives.firstDerivative (11/2) ≤ (m:ℝ)/(5*(n:ℝ)^2))
    (hU : (m:ℝ)/(5*(n:ℝ)^2) ≤ 1) :
    0 < sign (m%5)*((Borwein.polynomial n).coeff m:ℝ) := by
  obtain ⟨τ,hτ,hT,hs⟩ := saddle_in_closed_interval _ hL hU
  exact coefficient_sign n m τ hn hτ hT hs

end
end Borwein.CertifiedInteriorSign
