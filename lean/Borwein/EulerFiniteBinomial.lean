import Borwein.EulerQBinomial

set_option autoImplicit false

namespace Borwein.EulerFiniteBinomial
noncomputable section
open Complex EulerQBinomial

def term (q z : ℂ) (n k : ℕ) : ℂ := gaussian q n k*q^(k.choose 2)*z^k
def expansion (q z : ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.range (n+1), term q z n k
def product (q z : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1+z*q^j)

theorem term_zero (q z : ℂ) (n : ℕ) (hq : ‖q‖ < 1) : term q z n 0=1 := by
  simp [term, gaussian_zero q n hq]

theorem term_outside (q z : ℂ) (n k : ℕ) (hk : n < k) : term q z n k=0 := by
  simp [term, gaussian_outside q n k hk]

theorem term_succ (q z : ℂ) (n k : ℕ) (hq : ‖q‖ < 1) :
    term q z (n+1) (k+1)=term q (z*q) n (k+1)+z*term q (z*q) n k := by
  simp only [term, gaussian_succ q n k hq, Nat.choose_succ_succ', Nat.choose_one_right,
    pow_add, mul_pow, pow_one]
  ring

theorem expansion_shift (q z : ℂ) (n : ℕ) (hq : ‖q‖ < 1) :
    expansion q z n=(∑ k ∈ Finset.range (n+1), term q z n (k+1))+1 := by
  have h1 := Finset.sum_range_succ' (term q z n) (n+1)
  have h2 := Finset.sum_range_succ (term q z n) (n+1)
  rw [term_zero q z n hq] at h1
  rw [term_outside q z n (n+1) (by omega), add_zero] at h2
  exact h2.symm.trans h1

theorem expansion_succ (q z : ℂ) (n : ℕ) (hq : ‖q‖ < 1) :
    expansion q z (n+1)=(1+z)*expansion q (z*q) n := by
  have he : expansion q z (n+1)=
      (∑ k ∈ Finset.range (n+1), term q z (n+1) (k+1))+1 := by
    rw [expansion, Finset.sum_range_succ', term_zero q z (n+1) hq]
  rw [he]
  simp_rw [term_succ q z n _ hq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hs := expansion_shift q (z*q) n hq
  change _ = (1+z)*expansion q (z*q) n
  change expansion q (z*q) n = _ at hs
  change (∑ k ∈ Finset.range (n+1), term q (z*q) n (k+1)) +
    z*expansion q (z*q) n+1=(1+z)*expansion q (z*q) n
  linear_combination -hs

theorem product_succ (q z : ℂ) (n : ℕ) :
    product q z (n+1)=(1+z)*product q (z*q) n := by
  rw [product, Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_succ]
  ring

/-- Finite q-binomial theorem, proved directly for the analytic factors. -/
theorem finite_binomial (q z : ℂ) (n : ℕ) (hq : ‖q‖ < 1) :
    product q z n=expansion q z n := by
  induction n generalizing z with
  | zero => simp [product, expansion, term_zero q z 0 hq]
  | succ n ih => rw [product_succ, expansion_succ q z n hq, ih]

end
end Borwein.EulerFiniteBinomial
