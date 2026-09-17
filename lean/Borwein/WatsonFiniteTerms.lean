import Borwein.WatsonStepIdentification

set_option autoImplicit false

namespace Borwein.WatsonFiniteTerms
noncomputable section
open Complex EndpointEulerTail EulerQBinomial WatsonCertificateAlgebra WatsonPochhammer
  WatsonWeights WatsonStepIdentification

def row (q w : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  finiteEuler (2*n) q*weight q w k*(1-w^2*q*(q^k)^2)*
    inverse q ((w^2)⁻¹) ((n:ℤ)-k)*inverse q (w^2*q^2) ((n:ℤ)+k)

def transport (q w : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  finiteEuler (2*n) q*weight q w k*(w*q^(n+1)*(q^k)^2)*(1-w*q*q^k)*
    bracket q w (q^(n+1)) (q^k)*
    inverse q ((w^2)⁻¹) ((n:ℤ)-k)*inverse q (w^2*q^2) ((n+1:ℕ)+k)

def common (q w : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  finiteEuler (2*n) q*weight q w k*
    inverse q ((w^2)⁻¹) ((n+1:ℕ)-k)*inverse q (w^2*q^2) ((n+1:ℕ)+k)

theorem euler_two_step (q : ℂ) (hq0 : q ≠ 0) (n : ℕ) :
    finiteEuler (2*(n+1)) q=finiteEuler (2*n) q*(1-(q^(n+1))^2/q)*(1-(q^(n+1))^2) := by
  rw [show 2*(n+1)=(2*n+1)+1 by omega, pochhammer_succ, pochhammer_succ]
  have h2 : (q^(n+1))^2=q^(2*n+1+1) := by rw [← pow_mul]; congr 1; omega
  rw [h2, pow_succ q (2*n+1)]
  field_simp

theorem row_next (q w : ℂ) (hq0 : q ≠ 0) (n : ℕ) (k : ℤ) :
    row q w (n+1) k=common q w n k*
      ((1-(q^(n+1))^2/q)*(1-(q^(n+1))^2)*(1-w^2*q*(q^k)^2)) := by
  unfold row common
  rw [euler_two_step q hq0 n]
  ring

theorem row_current (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hA : ∀ j : ℕ, 1-(w^2)⁻¹*q^j ≠ 0) (hB : ∀ j : ℕ, 1-(w^2*q^2)*q^j ≠ 0)
    (n : ℕ) (k : ℤ) : row q w n k=common q w n k*
      ((1-w^2*q*(q^k)^2)*leftStep q w (q^(n+1)) (q^k)*rightStep q w (q^(n+1)) (q^k)) := by
  unfold row common
  rw [left_inverse_step q w hq hq0 hw hA n k, right_inverse_step q w hq hq0 hB n k]
  ring

theorem transport_current (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hA : ∀ j : ℕ, 1-(w^2)⁻¹*q^j ≠ 0) (n : ℕ) (k : ℤ) :
    transport q w n k=common q w n k*
      (w*q^(n+1)*(q^k)^2*(1-w*q*q^k)*bracket q w (q^(n+1)) (q^k)*
        leftStep q w (q^(n+1)) (q^k)) := by
  unfold transport common
  rw [left_inverse_step q w hq hq0 hw hA n k]
  ring

theorem transport_previous (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hB : ∀ j : ℕ, 1-(w^2*q^2)*q^j ≠ 0) (n : ℕ) (k : ℤ) :
    transport q w n (k-1)= -common q w n k*
      (q^(n+1)/(w^2*q*q^k)*(1-w*q^k)*bracket q w (q^(n+1)) (q^k/q)*
        rightStep q w (q^(n+1)) (q^k)) := by
  unfold transport common
  rw [weight_sub_one q w hq0 hw k, zpow_sub₀ hq0, zpow_one,
    show (n:ℤ)-(k-1)=((n+1:ℕ):ℤ)-k by omega,
    show ((n+1:ℕ):ℤ)+(k-1)=(n:ℤ)+k by omega,
    right_inverse_step q w hq hq0 hB n k]
  field_simp
  <;> ring

/-- Exact telescoping of the actual finite terms, valid at every integer index. -/
theorem telescoping (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hA : ∀ j : ℕ, 1-(w^2)⁻¹*q^j ≠ 0) (hB : ∀ j : ℕ, 1-(w^2*q^2)*q^j ≠ 0)
    (n : ℕ) (k : ℤ) :
    rowFactor q w (q^(n+1))*row q w (n+1) k-row q w n k=
      transport q w n k-transport q w n (k-1) := by
  rw [row_next q w hq0 n k, row_current q w hq hq0 hw hA hB n k,
    transport_current q w hq hq0 hw hA n k, transport_previous q w hq hq0 hw hB n k]
  have he := certificate_identity q w (q^(n+1)) (q^k) hq0 hw (zpow_ne_zero k hq0)
  linear_combination common q w n k*he

end
end Borwein.WatsonFiniteTerms
