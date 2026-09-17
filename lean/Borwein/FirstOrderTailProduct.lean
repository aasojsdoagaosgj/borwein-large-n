import Borwein.StableBorweinSeries

set_option autoImplicit false

namespace Borwein.FirstOrderTailProduct
noncomputable section
open Polynomial StableBorweinSeries

def shiftedCoeff (p : Polynomial ℤ) (m k : ℕ) : ℤ :=
  if k ≤ m then p.coeff (m-k) else 0

theorem factor_coefficient (p : Polynomial ℤ) (m k : ℕ) :
    (p*(1-X^k)).coeff m = p.coeff m-shiftedCoeff p m k := by
  rw [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow']
  rfl

theorem shifted_high_factor (p : Polynomial ℤ) (m k j L : ℕ)
    (hk : L ≤ k) (hj : L ≤ j) (hm : m < 2*L) :
    shiftedCoeff (p*(1-X^k)) m j = shiftedCoeff p m j := by
  unfold shiftedCoeff
  split_ifs with h
  · exact coeff_mul_high_factor p (m-j) k (by omega)
  · rfl

theorem product_coefficient {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι → ℕ) (p : Polynomial ℤ) (m L : ℕ)
    (hk : ∀ i ∈ s, L ≤ k i) (hm : m < 2*L) :
    (p*∏ i ∈ s, (1-X^(k i))).coeff m =
      p.coeff m-∑ i ∈ s, shiftedCoeff p m (k i) := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← mul_assoc]
    rw [ih _ (fun j hj => hk j (Finset.mem_insert_of_mem hj))]
    rw [factor_coefficient, Finset.sum_insert hi]
    have he : (∑ j ∈ s, shiftedCoeff (p*(1-X^(k i))) m (k j)) =
        ∑ j ∈ s, shiftedCoeff p m (k j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact shifted_high_factor p m (k i) (k j) L
        (hk i (Finset.mem_insert_self _ _)) (hk j (Finset.mem_insert_of_mem hj)) hm
    rw [he]
    ring

theorem polynomial_append (n t : ℕ) :
    Borwein.polynomial (n+t) = Borwein.polynomial n*
      ∏ p ∈ (Finset.range t).product (Finset.univ : Finset (Fin 4)),
        (1-X^(Borwein.exponent (n+p.1) p.2)) := by
  rw [Borwein.polynomial, Finset.prod_range_add]
  simp only [Finset.product_eq_sprod]
  rw [Finset.prod_product (Finset.range t) (Finset.univ : Finset (Fin 4))
    (fun p : ℕ × Fin 4 => (1-X^(Borwein.exponent (n+p.1) p.2) : Polynomial ℤ))]
  rfl

theorem first_tail_coefficient (n t m : ℕ) (hm : m < 10*n+2) :
    (Borwein.polynomial (n+t)).coeff m = (Borwein.polynomial n).coeff m-
      ∑ i ∈ Finset.range t, ∑ a : Fin 4,
        shiftedCoeff (Borwein.polynomial n) m (Borwein.exponent (n+i) a) := by
  rw [polynomial_append]
  have he := product_coefficient ((Finset.range t).product (Finset.univ : Finset (Fin 4)))
    (fun p => Borwein.exponent (n+p.1) p.2) (Borwein.polynomial n) m (5*n+1)
    (by intro p _; unfold Borwein.exponent; omega) (by omega)
  simp only [Finset.product_eq_sprod] at he
  rw [Finset.sum_product (Finset.range t) (Finset.univ : Finset (Fin 4))
    (fun p : ℕ × Fin 4 => shiftedCoeff (Borwein.polynomial n) m (Borwein.exponent (n+p.1) p.2))] at he
  exact he

end
end Borwein.FirstOrderTailProduct
