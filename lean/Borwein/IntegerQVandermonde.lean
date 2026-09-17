import Borwein.CiglerWeights

set_option autoImplicit false

namespace Borwein.IntegerQVandermonde
noncomputable section
open Complex IntegerQBinomial CiglerWeights

def convolution (q : ℂ) (n m : ℕ) (k : ℤ) : ℂ :=
  ∑' j : ℤ, q^(((n:ℤ)-j)*(k-j))*choose q n j*choose q m (k-j)

theorem column_summable (q : ℂ) (n : ℕ) (f : ℤ → ℂ) :
    Summable (fun j : ℤ => f j*choose q n j) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 0 (n:ℤ))
  intro j hj
  have h : j < 0 ∨ (n:ℤ) < j := by
    simpa only [Finset.mem_Icc, not_and_or, not_le] using hj
  rcases h with h | h
  · rw [choose_negative q n j h, mul_zero]
  · rw [choose_above q n j h, mul_zero]

theorem term_summable (q : ℂ) (n m : ℕ) (k : ℤ) :
    Summable (fun j : ℤ => q^(((n:ℤ)-j)*(k-j))*choose q n j*choose q m (k-j)) := by
  apply (column_summable q n (fun j => q^(((n:ℤ)-j)*(k-j))*choose q m (k-j))).congr
  intro j
  ring

theorem add_one_reindex (f : ℤ → ℂ) : (∑' j : ℤ, f (j+1)) = ∑' j : ℤ, f j := by
  let e : ℤ ≃ ℤ := {
    toFun := fun j => j+1
    invFun := fun j => j-1
    left_inv := by intro j; change (j+1)-1=j; ring
    right_inv := by intro j; change (j-1)+1=j; ring }
  exact e.tsum_eq f

theorem convolution_zero (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) (k : ℤ) :
    convolution q 0 m k = choose q m k := by
  rw [convolution, tsum_eq_single 0]
  · simp [choose_zero_column q 0 hq]
  · intro j hj
    rw [choose_zero_row q j hq, if_neg hj, mul_zero, zero_mul]

theorem convolution_recurrence (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (n m : ℕ) (k : ℤ) :
    convolution q (n+1) m k = convolution q n m (k-1)+q^k*convolution q n m k := by
  let f : ℤ → ℂ := fun j => q^(((n:ℤ)+1-j)*(k-j))*choose q n (j-1)*choose q m (k-j)
  have hf (j : ℤ) : f (j+1)=q^(((n:ℤ)-j)*((k-1)-j))*choose q n j*choose q m ((k-1)-j) := by
    dsimp [f]
    rw [show j+1-1=j by ring, show (n:ℤ)+1-(j+1)=(n:ℤ)-j by ring,
      show k-(j+1)=(k-1)-j by ring]
  have hfs : Summable f := by
    apply summable_of_ne_finset_zero (s := Finset.Icc 1 ((n:ℤ)+1))
    intro j hj
    have hj' : j-1 < 0 ∨ (n:ℤ) < j-1 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hj
      omega
    dsimp [f]
    rcases hj' with h | h
    · rw [choose_negative q n (j-1) h, mul_zero, zero_mul]
    · rw [choose_above q n (j-1) h, mul_zero, zero_mul]
  have ht (j : ℤ) : q^((((n+1:ℕ):ℤ)-j)*(k-j))*choose q (n+1) j*choose q m (k-j) =
      f j+q^k*(q^(((n:ℤ)-j)*(k-j))*choose q n j*choose q m (k-j)) := by
    rw [pascal_left q n j hq]
    dsimp [f]
    push_cast
    have he : ((n:ℤ)+1-j)*(k-j)+j=k+((n:ℤ)-j)*(k-j) := by ring
    have hh : q^(((n:ℤ)+1-j)*(k-j))*q^j = q^k*q^(((n:ℤ)-j)*(k-j)) := by
      rw [← zpow_add₀ hq0, he, zpow_add₀ hq0]
    linear_combination (choose q n j*choose q m (k-j))*hh
  change (∑' j : ℤ, q^((((n+1:ℕ):ℤ)-j)*(k-j))*choose q (n+1) j*choose q m (k-j)) = _
  simp_rw [ht]
  rw [Summable.tsum_add hfs ((term_summable q n m k).mul_left _), tsum_mul_left]
  have he : (∑' j : ℤ, f j) = convolution q n m (k-1) := by
    rw [← add_one_reindex f]
    simp only [hf, convolution]
  rw [he]
  rfl

theorem vandermonde (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n m : ℕ) (k : ℤ) :
    convolution q n m k = choose q (n+m) k := by
  induction n generalizing k with
  | zero => simpa using convolution_zero q hq m k
  | succ n ih =>
    rw [convolution_recurrence q hq hq0 n m k, ih, ih,
      show n+1+m=(n+m)+1 by omega, pascal_left q (n+m) k hq]

end
end Borwein.IntegerQVandermonde
