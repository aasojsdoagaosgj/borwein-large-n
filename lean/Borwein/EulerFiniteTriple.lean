import Borwein.EulerFiniteBinomial

set_option autoImplicit false

namespace Borwein.EulerFiniteTriple
noncomputable section
open Complex EulerQBinomial EulerFiniteBinomial

def reverseHalf (q z : ℂ) (n : ℕ) : ℂ := ∏ j ∈ Finset.range n, (1-z/q^(j+1))

theorem product_append (q z : ℂ) (n : ℕ) :
    product q z (n+1)=product q z n*(1+z*q^n) := by
  simp [product, Finset.prod_range_succ]

theorem product_add (q z : ℂ) (n m : ℕ) :
    product q z (n+m)=product q z n*product q (z*q^n) m := by
  rw [product, Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [pow_add]
  ring

theorem reverseHalf_succ (q z : ℂ) (n : ℕ) :
    reverseHalf q z (n+1)=reverseHalf q z n*(1-z/q^(n+1)) := by
  simp [reverseHalf, Finset.prod_range_succ]

theorem reflected_product (q z : ℂ) (n : ℕ) (hq : q ≠ 0) :
    product q (-z/q^n) n=reverseHalf q z n := by
  unfold product reverseHalf
  rw [← Finset.prod_range_reflect (fun j => 1+(-z/q^n)*q^j) n]
  apply Finset.prod_congr rfl
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  have hp : q^(n-1-j)*q^(j+1)=q^n := by rw [← pow_add]; congr 1; omega
  field_simp
  linear_combination -z*hp

theorem reciprocal_product (q z : ℂ) (n : ℕ) (hq : q ≠ 0) (hz : z ≠ 0) :
    q^((n+1).choose 2)*reverseHalf q z n=(-z)^n*product q (-q/z) n := by
  induction n with
  | zero => simp [reverseHalf, product]
  | succ n ih =>
    have ht : (n+1+1).choose 2=(n+1).choose 2+(n+1) := by
      rw [Nat.choose_succ_succ']
      simp [add_comm]
    rw [ht, pow_add, reverseHalf_succ]
    calc
      _ = (q^((n+1).choose 2)*reverseHalf q z n)*(q^(n+1)-z) := by
        field_simp
        <;> ring
      _ = ((-z)^n*product q (-q/z) n)*(q^(n+1)-z) := by rw [ih]
      _ = (-z)^(n+1)*product q (-q/z) (n+1) := by
        rw [product_append, pow_succ, pow_succ]
        field_simp
        <;> ring

/-- Exact finite precursor of the Jacobi triple product. No limiting identity is assumed. -/
theorem finite_triple_product (q z : ℂ) (n : ℕ) (hq : q ≠ 0) (hz : z ≠ 0) :
    q^((n+1).choose 2)*product q (-z/q^n) (2*n)=
      (-z)^n*product q (-z) n*product q (-q/z) n := by
  rw [show 2*n=n+n by omega, product_add, reflected_product q z n hq]
  have he : (-z/q^n)*q^n=-z := by field_simp
  rw [he, ← mul_assoc, reciprocal_product q z n hq hz]
  ring

/-- The exact finite sum that will be centered and passed to the limit. -/
theorem finite_triple_sum (q z : ℂ) (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hz : z ≠ 0) :
    q^((n+1).choose 2)*expansion q (-z/q^n) (2*n)=
      (-z)^n*product q (-z) n*product q (-q/z) n := by
  rw [← finite_binomial q (-z/q^n) (2*n) hq]
  exact finite_triple_product q z n hq0 hz

end
end Borwein.EulerFiniteTriple
