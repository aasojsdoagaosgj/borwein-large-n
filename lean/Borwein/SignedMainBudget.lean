import Borwein.CombinedPhaseSign
import Borwein.BulkSignCriterion

set_option autoImplicit false

namespace Borwein.SignedMainBudget
noncomputable section
open RadialDerivatives ActualPhaseTaylor AmplitudeTaylor EMUniformBounds
  GaussianNormalization CertifiedBulkRemainder ExplicitPhaseProfile CombinedPhaseSign

def relativeBudget (τ : ℝ) : ℝ :=
  (240*W 4 τ/(32*(39/100:ℝ)^2*(secondDerivative τ)^2)+
    2645*(W 3 τ)^2/(192*(39/100:ℝ)^3*(secondDerivative τ)^3)+
    EMUniformBounds.radius τ (2/5)/30)/Real.sqrt (39/50:ℝ)

def absoluteBudget (τ : ℝ) : ℝ :=
  (4*(23*a1 τ*W 3 τ/(8*(39/100:ℝ)^2*(secondDerivative τ)^2)+
      a2 τ/(2*(39/100:ℝ)*secondDerivative τ))+
    EMUniformBounds.radius τ (2/5)/30*((8/5:ℝ)*a1 τ)+
    (1232/1875:ℝ)*EMUniformBounds.radius τ (2/5)*Real.exp (-τ))/Real.sqrt (39/50:ℝ)

theorem budgets_nonneg (τ : ℝ) : 0 ≤ relativeBudget τ ∧ 0 ≤ absoluteBudget τ := by
  have hV := (secondDerivative_pos τ).le
  have hW3 := W_nonneg 3 τ
  have hW4 := W_nonneg 4 τ
  have ha1 := (CombinedGaussianError.amplitude_budgets_nonneg τ).1
  have ha2 := (CombinedGaussianError.amplitude_budgets_nonneg τ).2
  unfold relativeBudget absoluteBudget EMUniformBounds.radius
  constructor <;> positivity

theorem mainBudget_affine (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    mainBudget FivePoleCircle.zeta a τ =
      (sign a*phase a τ)*relativeBudget τ+absoluteBudget τ := by
  unfold mainBudget errorCoefficient coreBudget thetaBudget relativeBudget absoluteBudget
  rw [psi_norm_eq_signed a ha τ hτ]
  ring

/-- Three certified real bounds suffice: a phase lower bound and two budget upper bounds.
The arithmetic condition keeps the same phase in the main term and the relative error. -/
theorem certificate_margin (a : ℕ) (ha : a < 5) (τ P R B : ℝ) (hτ : 0 ≤ τ)
    (hP : 0 < P) (hp : P ≤ sign a*phase a τ)
    (hr : relativeBudget τ ≤ R) (hb : absoluteBudget τ ≤ B) (hR : R < 31147)
    (hcert : B+31147*(9/100000:ℝ) < (31147-R)*P) :
    mainBudget FivePoleCircle.zeta a τ/31147+(9/100000:ℝ) <
      sign a*(CombinedAmplitude.psi FivePoleCircle.zeta a (τ:ℂ)).re := by
  have hp0 : 0 ≤ sign a*phase a τ := (hP.trans_le hp).le
  have hrel := mul_le_mul_of_nonneg_left hr hp0
  have hgap := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ 31147-R)
  rw [mainBudget_affine a ha τ hτ,psi_eq_profile a ha τ hτ,Complex.ofReal_re]
  nlinarith

theorem signed_coefficient_from_certificate (n m : ℕ) (τ P R B : ℝ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2))
    (hP : 0 < P) (hp : P ≤ sign (m%5)*phase (m%5) τ)
    (hr : relativeBudget τ ≤ R) (hb : absoluteBudget τ ≤ B) (hR : R < 31147)
    (hcert : B+31147*(9/100000:ℝ) < (31147-R)*P) :
    0 < sign (m%5)*((Borwein.polynomial n).coeff m:ℝ) := by
  apply BulkSignCriterion.signed_coefficient n m τ (sign (m%5)) hn hτ hT hs
  · by_cases h : m%5 = 0
    · exact Or.inl (by simp [sign,h])
    · exact Or.inr (by simp [sign,h])
  · exact certificate_margin (m%5) (Nat.mod_lt _ (by norm_num)) τ P R B hτ hP hp hr hb hR hcert

end
end Borwein.SignedMainBudget
