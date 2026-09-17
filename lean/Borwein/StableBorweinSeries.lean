import Borwein.Reciprocity
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false

namespace Borwein.StableBorweinSeries
noncomputable section
open Polynomial

theorem coeff_mul_high_factor (p : Polynomial ℤ) (m k : ℕ) (hk : m < k) :
    (p*(1-X^k)).coeff m = p.coeff m := by
  rw [mul_sub, mul_one, coeff_sub, coeff_mul_X_pow']
  simp [Nat.not_le.mpr hk]

theorem coeff_mul_high_product {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι → ℕ) (p : Polynomial ℤ) (m : ℕ) (hk : ∀ i ∈ s, m < k i) :
    (p*∏ i ∈ s, (1-X^(k i))).coeff m = p.coeff m := by
  induction s using Finset.induction_on generalizing p with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, ← mul_assoc]
    rw [ih _ (fun j hj => hk j (Finset.mem_insert_of_mem hj))]
    exact coeff_mul_high_factor p m (k i) (hk i (Finset.mem_insert_self _ _))

theorem coefficient_step (n m : ℕ) (hm : m ≤ 5*n) :
    (Borwein.polynomial (n+1)).coeff m = (Borwein.polynomial n).coeff m := by
  rw [Borwein.polynomial, Finset.prod_range_succ]
  change (Borwein.polynomial n*Borwein.block n).coeff m = _
  unfold Borwein.block
  exact coeff_mul_high_product Finset.univ (Borwein.exponent n) _ m (by
    intro a _
    unfold Borwein.exponent
    omega)

theorem coefficient_stable (n N m : ℕ) (hn : n ≤ N) (hm : m ≤ 5*n) :
    (Borwein.polynomial N).coeff m = (Borwein.polynomial n).coeff m := by
  induction N, hn using Nat.le_induction with
  | base => rfl
  | succ N hN ih => rw [coefficient_step N m (by omega), ih]

def stableCoeff (m : ℕ) : ℤ := (Borwein.polynomial (m+1)).coeff m
def series : PowerSeries ℤ := PowerSeries.mk stableCoeff

theorem stableCoeff_eq (n m : ℕ) (hm : m ≤ 5*n) :
    stableCoeff m = (Borwein.polynomial n).coeff m := by
  have h1 := coefficient_stable n (n+m+1) m (by omega) hm
  have h2 := coefficient_stable (m+1) (n+m+1) m (by omega) (by omega)
  exact h2.symm.trans h1

theorem coeff_series (m : ℕ) : PowerSeries.coeff m series = stableCoeff m := by
  simp [series]

theorem series_matches_finite (n m : ℕ) (hm : m ≤ 5*n) :
    PowerSeries.coeff m series = (Borwein.polynomial n).coeff m := by
  rw [coeff_series]
  exact stableCoeff_eq n m hm

end
end Borwein.StableBorweinSeries
