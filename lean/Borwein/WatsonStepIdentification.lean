import Borwein.WatsonCertificateAlgebra
import Borwein.WatsonPochhammer
import Borwein.WatsonWeights

set_option autoImplicit false

namespace Borwein.WatsonStepIdentification
noncomputable section
open Complex WatsonCertificateAlgebra WatsonPochhammer

theorem left_identification (q w : ℂ) (hq : q ≠ 0) (hw : w ≠ 0) (n : ℕ) (k : ℤ) :
    (1-q^((n+1:ℕ)-k))*(1-(w^2)⁻¹*q^((n+1:ℕ)-k-1))=
      leftStep q w (q^(n+1)) (q^k) := by
  have h1 : ((n+1:ℕ):ℤ)-k-1=(n:ℤ)-k := by omega
  rw [h1, zpow_sub₀ hq, zpow_natCast, zpow_sub₀ hq, zpow_natCast]
  unfold leftStep
  rw [pow_succ]
  field_simp
  <;> ring

theorem right_identification (q w : ℂ) (hq : q ≠ 0) (n : ℕ) (k : ℤ) :
    (1-q^((n+1:ℕ)+k))*(1-(w^2*q^2)*q^((n+1:ℕ)+k-1))=
      rightStep q w (q^(n+1)) (q^k) := by
  have h1 : ((n+1:ℕ):ℤ)+k-1=(n:ℤ)+k := by omega
  rw [h1, zpow_add₀ hq, zpow_natCast, zpow_add₀ hq, zpow_natCast]
  unfold rightStep
  rw [pow_succ]
  ring

theorem left_inverse_step (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hA : ∀ j : ℕ, 1-(w^2)⁻¹*q^j ≠ 0) (n : ℕ) (k : ℤ) :
    inverse q ((w^2)⁻¹) ((n:ℤ)-k)=leftStep q w (q^(n+1)) (q^k)*
      inverse q ((w^2)⁻¹) ((n+1:ℕ)-k) := by
  have hh := inverse_step q ((w^2)⁻¹) hq hA (((n+1:ℕ):ℤ)-k)
  rw [left_identification q w hq0 hw n k] at hh
  simpa only [show ((n+1:ℕ):ℤ)-k-1=(n:ℤ)-k by omega] using hh

theorem right_inverse_step (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hB : ∀ j : ℕ, 1-(w^2*q^2)*q^j ≠ 0) (n : ℕ) (k : ℤ) :
    inverse q (w^2*q^2) ((n:ℤ)+k)=rightStep q w (q^(n+1)) (q^k)*
      inverse q (w^2*q^2) ((n+1:ℕ)+k) := by
  have hh := inverse_step q (w^2*q^2) hq hB (((n+1:ℕ):ℤ)+k)
  rw [right_identification q w hq0 n k] at hh
  simpa only [show ((n+1:ℕ):ℤ)+k-1=(n:ℤ)+k by omega] using hh

end
end Borwein.WatsonStepIdentification
