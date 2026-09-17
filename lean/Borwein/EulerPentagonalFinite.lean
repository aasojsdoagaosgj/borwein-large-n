import Borwein.EulerFiniteTriple
import Mathlib.Combinatorics.Enumerative.Pentagonal

set_option autoImplicit false

namespace Borwein.EulerPentagonalFinite
noncomputable section
open Complex EndpointEulerTail EulerQBinomial EulerFiniteBinomial EulerFiniteTriple

/-- Splitting every third Euler factor is an exact finite identity. -/
theorem residue_factors (q : ℂ) (n : ℕ) :
    finiteEuler (3*n) q=
      finiteEuler n (q^3)*product (q^3) (-q) n*product (q^3) (-q^2) n := by
  induction n with
  | zero => simp [finiteEuler, product]
  | succ n ih =>
    rw [show 3*(n+1)=((3*n+1)+1)+1 by omega, pochhammer_succ, pochhammer_succ,
      pochhammer_succ, ih, pochhammer_succ, product_append, product_append]
    simp only [← pow_mul, Nat.mul_add, Nat.mul_one, pow_add, pow_one]
    ring

/-- A finite Gaussian-binomial expansion of the actual Euler product. -/
theorem finite_euler_sum (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (-q)^n*finiteEuler (3*n) q=
      finiteEuler n (q^3)*(q^3)^((n+1).choose 2)*
        expansion (q^3) (-q/(q^3)^n) (2*n) := by
  have hq3 : ‖q^3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have ht := finite_triple_sum (q^3) q n hq3 (pow_ne_zero _ hq0) hq0
  have he : -(q^3)/q=-(q^2) := by field_simp <;> ring
  rw [he] at ht
  rw [residue_factors]
  linear_combination -(finiteEuler n (q^3))*ht

/-- Generalized pentagonal numbers never lie in the two weak residue classes. -/
theorem pentagonal_residues (j : ℤ) : pentagonal j % 5=0 ∨ pentagonal j % 5=1 ∨ pentagonal j % 5=2 := by
  have he := two_mul_natCast_pentagonal j
  have hm := congrArg (fun z : ℤ => z%5) he
  have hj : 0 ≤ j%5 ∧ j%5 < 5 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rcases hj with ⟨hj0, hj5⟩
  rw [Int.mul_emod 2 _, Int.mul_emod j _, Int.sub_emod, Int.mul_emod 3 j] at hm
  interval_cases h : j%5 <;> norm_num [h] at hm <;> omega

end
end Borwein.EulerPentagonalFinite
