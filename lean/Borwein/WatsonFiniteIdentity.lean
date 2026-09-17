import Borwein.WatsonFiniteTerms

set_option autoImplicit false

namespace Borwein.WatsonFiniteIdentity
noncomputable section
open Complex EndpointEulerTail EulerFiniteBinomial EulerFiniteTriple WatsonCertificateAlgebra
  WatsonPochhammer WatsonWeights WatsonFiniteTerms

def rhs (q w : ℂ) (n : ℕ) : ℂ := (1-w^2*q)/(product q (-w⁻¹) n*product q (-(w*q)) n)

theorem row_outside (q w : ℂ) (n : ℕ) (k : ℤ) (hk : ¬ (-(n:ℤ) ≤ k ∧ k ≤ (n:ℤ))) :
    row q w n k=0 := by
  have h : (n:ℤ)-k < 0 ∨ (n:ℤ)+k < 0 := by omega
  unfold row
  rcases h with h | h
  · rw [inverse_negative _ _ _ h, mul_zero, zero_mul]
  · rw [inverse_negative _ _ _ h, mul_zero]

theorem row_summable (q w : ℂ) (n : ℕ) : Summable (row q w n) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(n:ℤ)) (n:ℤ))
  intro k hk
  exact row_outside q w n k (by simpa only [Finset.mem_Icc] using hk)

theorem transport_summable (q w : ℂ) (n : ℕ) : Summable (transport q w n) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (-(n:ℤ)-1) (n:ℤ))
  intro k hk
  have h : (n:ℤ)-k < 0 ∨ ((n+1:ℕ):ℤ)+k < 0 := by
    simp only [Finset.mem_Icc] at hk
    omega
  unfold transport
  rcases h with h | h
  · rw [inverse_negative _ _ _ h, mul_zero, zero_mul]
  · rw [inverse_negative _ _ _ h, mul_zero]

theorem shift_sum (f : ℤ → ℂ) : (∑' k : ℤ, f (k-1))=∑' k : ℤ, f k := by
  let e : ℤ ≃ ℤ := {
    toFun := fun k => k-1
    invFun := fun k => k+1
    left_inv := by intro k; change k-1+1=k; ring
    right_inv := by intro k; change k+1-1=k; ring }
  exact e.tsum_eq f

theorem sum_recurrence (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hA : ∀ j : ℕ, 1-(w^2)⁻¹*q^j ≠ 0) (hB : ∀ j : ℕ, 1-(w^2*q^2)*q^j ≠ 0)
    (n : ℕ) : rowFactor q w (q^(n+1))*(∑' k : ℤ, row q w (n+1) k)=∑' k : ℤ, row q w n k := by
  have ht := transport_summable q w n
  have hshift : Summable (fun k : ℤ => transport q w n (k-1)) := by
    exact ht.comp_injective (by intro i j he; change i-1=j-1 at he; omega)
  apply sub_eq_zero.mp
  calc
    _ = ∑' k : ℤ, (rowFactor q w (q^(n+1))*row q w (n+1) k-row q w n k) := by
      rw [((row_summable q w (n+1)).mul_left _).tsum_sub (row_summable q w n), tsum_mul_left]
    _ = ∑' k : ℤ, (transport q w n k-transport q w n (k-1)) :=
      tsum_congr (fun k => telescoping q w hq hq0 hw hA hB n k)
    _ = 0 := by rw [ht.tsum_sub hshift, shift_sum]; ring

theorem sum_zero (q w : ℂ) : (∑' k : ℤ, row q w 0 k)=1-w^2*q := by
  rw [tsum_eq_single (0:ℤ) (fun k hk => row_outside q w 0 k (by omega))]
  simp [row, finiteEuler, weight_zero, inverse_zero]

theorem rowFactor_eq (q w : ℂ) (hq0 : q ≠ 0) (hw : w ≠ 0) (n : ℕ) :
    rowFactor q w (q^(n+1))=(1-w⁻¹*q^n)*(1-(w*q)*q^n) := by
  unfold rowFactor
  rw [pow_succ]
  field_simp

theorem rhs_recurrence (q w : ℂ) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hC : ∀ j : ℕ, 1-w⁻¹*q^j ≠ 0) (hD : ∀ j : ℕ, 1-(w*q)*q^j ≠ 0)
    (n : ℕ) : rowFactor q w (q^(n+1))*rhs q w (n+1)=rhs q w n := by
  rw [rowFactor_eq q w hq0 hw n]
  unfold rhs
  rw [product_append, product_append]
  simp only [neg_mul, ← sub_eq_add_neg]
  have cancel (P R A B c : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) :
      (A*B)*(c/((P*A)*(R*B)))=c/(P*R) := by
    rw [← mul_div_assoc, show (P*A)*(R*B)=(A*B)*(P*R) by ring]
    exact mul_div_mul_left _ _ (mul_ne_zero hA hB)
  exact cancel _ _ _ _ _ (hC n) (hD n)

/-- The finite Watson identity obtained by summing the exact telescoper. -/
theorem finite_watson (q w : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hw : w ≠ 0)
    (hA : ∀ j : ℕ, 1-(w^2)⁻¹*q^j ≠ 0) (hB : ∀ j : ℕ, 1-(w^2*q^2)*q^j ≠ 0)
    (hC : ∀ j : ℕ, 1-w⁻¹*q^j ≠ 0) (hD : ∀ j : ℕ, 1-(w*q)*q^j ≠ 0)
    (n : ℕ) : (∑' k : ℤ, row q w n k)=rhs q w n := by
  induction n with
  | zero => simp [sum_zero, rhs, product]
  | succ n ih =>
    have hrow : rowFactor q w (q^(n+1)) ≠ 0 := by
      rw [rowFactor_eq q w hq0 hw n]
      exact mul_ne_zero (hC n) (hD n)
    apply mul_left_cancel₀ hrow
    rw [sum_recurrence q w hq hq0 hw hA hB n, rhs_recurrence q w hq0 hw hC hD n]
    exact ih

end
end Borwein.WatsonFiniteIdentity
