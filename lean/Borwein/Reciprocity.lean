import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Constant-independent facts for the finite Borwein product

This file formalizes the algebraic reciprocity used in (1.3) and the arithmetic
observation immediately following it in `round4-6/manuscript.md`.  No analytic
estimate or numerical threshold occurs here.
-/

namespace Borwein

open scoped BigOperators
open Finset Polynomial

/-- The exponent in block `i` and nonzero residue `a + 1` modulo five. -/
def exponent (i : ℕ) (a : Fin 4) : ℕ := 5 * i + (a : ℕ) + 1

/-- One block of four factors with exponents `5i+1, ..., 5i+4`. -/
noncomputable def block (i : ℕ) : ℤ[X] :=
  ∏ a : Fin 4, (1 - X ^ exponent i a)

/-- The finite Borwein product `∏_{1 ≤ j ≤ 5n, 5 ∤ j} (1-q^j)`. -/
noncomputable def polynomial (n : ℕ) : ℤ[X] :=
  ∏ i ∈ range n, block i

/-- The degree claimed in the manuscript. -/
def totalDegree (n : ℕ) : ℕ := 10 * n ^ 2

private lemma exponent_pos (i : ℕ) (a : Fin 4) : 0 < exponent i a := by
  simp [exponent]

private lemma factor_ne_zero (i : ℕ) (a : Fin 4) :
    (1 - X ^ exponent i a : ℤ[X]) ≠ 0 := by
  intro h
  have hcoeff := congrArg (fun p : ℤ[X] ↦ p.coeff 0) h
  have hzero : 0 ≠ exponent i a := Nat.ne_of_lt (exponent_pos i a)
  simp [hzero] at hcoeff

private lemma natDegree_factor (i : ℕ) (a : Fin 4) :
    (1 - X ^ exponent i a : ℤ[X]).natDegree = exponent i a := by
  rw [show (1 - X ^ exponent i a : ℤ[X]) =
    -(X ^ exponent i a - C 1) by simp only [C_1]; ring]
  simp only [Polynomial.natDegree_neg]
  exact Polynomial.natDegree_X_pow_sub_C

private lemma reverse_factor (i : ℕ) (a : Fin 4) :
    (1 - X ^ exponent i a : ℤ[X]).reverse = -(1 - X ^ exponent i a) := by
  rw [Polynomial.reverse, natDegree_factor, Polynomial.reflect_sub]
  simp [Polynomial.reflect_monomial, Polynomial.revAt]

private lemma reverse_prod {ι : Type*} [DecidableEq ι] {s : Finset ι} (f : ι → ℤ[X]) :
    (∏ i ∈ s, f i).reverse = ∏ i ∈ s, (f i).reverse := by
  induction s using Finset.induction_on with
  | empty => simp only [prod_empty, ← Polynomial.C_1, Polynomial.reverse_C]
  | @insert x s hx ih =>
      simp only [prod_insert hx]
      rw [Polynomial.reverse_mul_of_domain, ih]

lemma reverse_block (i : ℕ) : (block i).reverse = block i := by
  unfold block
  rw [reverse_prod]
  simp_rw [reverse_factor]
  rw [Fin.prod_univ_four, Fin.prod_univ_four]
  ring

/-- The finite Borwein product is self-reciprocal. -/
theorem reverse_polynomial (n : ℕ) : (polynomial n).reverse = polynomial n := by
  unfold polynomial
  rw [reverse_prod]
  simp_rw [reverse_block]

private lemma block_ne_zero (i : ℕ) : block i ≠ 0 := by
  unfold block
  exact Finset.prod_ne_zero_iff.mpr (fun a _ ↦ factor_ne_zero i a)

private lemma natDegree_block (i : ℕ) :
    (block i).natDegree = 20 * i + 10 := by
  unfold block
  rw [Polynomial.natDegree_prod]
  · simp_rw [natDegree_factor]
    simp [exponent, Fin.sum_univ_four]
    omega
  · intro a ha
    exact factor_ne_zero i a

private lemma polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 := by
  unfold polynomial
  exact Finset.prod_ne_zero_iff.mpr (fun i hi ↦ block_ne_zero i)

/- The explicit degree calculation is kept separate so that later analytic
   constant improvements cannot affect the reciprocity interface. -/
lemma natDegree_polynomial (n : ℕ) :
    (polynomial n).natDegree = totalDegree n := by
  unfold polynomial totalDegree
  rw [Polynomial.natDegree_prod]
  · simp_rw [natDegree_block]
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  · intro i hi
    exact block_ne_zero i

/-- Coefficient form of equation (1.3). -/
theorem coeff_reflection (n m : ℕ) (hm : m ≤ totalDegree n) :
    (polynomial n).coeff m = (polynomial n).coeff (totalDegree n - m) := by
  have hdeg := natDegree_polynomial n
  have hrev := congrArg (fun p : ℤ[X] ↦ p.coeff m) (reverse_polynomial n)
  rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le hm] at hrev
  exact hrev.symm

/-- Reflection about `10n²` preserves divisibility by five. -/
theorem five_dvd_reflection_iff (n m : ℕ) (hm : m ≤ totalDegree n) :
    5 ∣ totalDegree n - m ↔ 5 ∣ m := by
  apply Nat.dvd_sub_iff_right hm
  refine ⟨2 * n ^ 2, ?_⟩
  simp [totalDegree]
  ring

/-- Therefore the target sign class in (1.1) is unchanged by reflection. -/
theorem sign_class_reflection (n m : ℕ) (hm : m ≤ totalDegree n) :
    (if 5 ∣ totalDegree n - m then (1 : ℤ) else -1) =
      if 5 ∣ m then 1 else -1 := by
  simp only [five_dvd_reflection_iff n m hm]

end Borwein
