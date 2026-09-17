import Borwein.CiglerAdjacent

set_option autoImplicit false

namespace Borwein.CiglerIdentity
noncomputable section
open Complex IntegerQBinomial CiglerWeights CiglerAdjacent

theorem value_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℤ) : value q 0 k=choose q 0 k := by
  have ht : ∀ j : ℤ, j ≠ 0 → weight q j*choose q 0 (k-j)*choose q 0 (k+j)=0 := by
    intro j hj
    by_cases h1 : k-j=0
    · have h2 : k+j ≠ 0 := by omega
      rw [choose_zero_row q (k+j) hq, if_neg h2, mul_zero]
    · rw [choose_zero_row q (k-j) hq, if_neg h1, mul_zero, zero_mul]
  rw [value, tsum_eq_single 0 ht]
  simp only [weight, zpow_zero, pentagonal, Int.mul_zero, Int.zero_mul, Int.zero_ediv,
    Int.toNat_zero, Int.natCast_zero, mul_one, zero_add, sub_zero, add_zero]
  rw [choose_zero_row q k hq]
  split_ifs <;> norm_num

theorem value_recurrence (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n : ℕ) (k : ℤ) :
    value q (n+1) k = value q n k+q^((n:ℤ)+1-k)*value q n (k-1) := by
  have ht (j : ℤ) : weight q j*choose q (n+1) (k-j)*choose q (n+1) (k+j) =
      weight q j*choose q n (k-j)*choose q (n+1) (k+j)+
      q^((n:ℤ)+1-k)*(weight q j*q^j*choose q n ((k-1)-j)*choose q (n+1) ((k-1)+j+1)) := by
    rw [pascal_right q n (k-j) hq,
      show (n:ℤ)+1-(k-j)=((n:ℤ)+1-k)+j by ring, zpow_add₀ hq0,
      show k-j-1=(k-1)-j by ring, show (k-1)+j+1=k+j by ring]
    ring
  have hs := product_summable q n (n+1) (k-1) k (fun j => weight q j*q^j)
  have hs' : Summable (fun j : ℤ => weight q j*q^j*choose q n ((k-1)-j)*choose q (n+1) ((k-1)+j+1)) := by
    convert hs using 1
    ext j
    rw [show (k-1)+j+1=k+j by ring]
  change (∑' j : ℤ, weight q j*choose q (n+1) (k-j)*choose q (n+1) (k+j)) = _
  simp_rw [ht]
  rw [Summable.tsum_add (product_summable q n (n+1) k k (weight q)) (hs'.mul_left _),
    tsum_mul_left, adjacent_right q hq hq0 n k, adjacent_shift q hq hq0 n (k-1)]

theorem value_eq_choose (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n : ℕ) (k : ℤ) :
    value q n k = choose q n k := by
  induction n generalizing k with
  | zero => exact value_zero q hq k
  | succ n ih => rw [value_recurrence q hq hq0 n k, ih, ih, pascal_right q n k hq]

theorem finite_alternating_identity (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n k : ℕ) :
    (∑ j ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), weight q j*
      choose q n ((k:ℤ)-j)*choose q n ((k:ℤ)+j)) = EulerQBinomial.gaussian q n k := by
  have hs : (∑' j : ℤ, weight q j*choose q n ((k:ℤ)-j)*choose q n ((k:ℤ)+j)) =
      ∑ j ∈ Finset.Icc (-(k:ℤ)) (k:ℤ), weight q j*
        choose q n ((k:ℤ)-j)*choose q n ((k:ℤ)+j) := by
    apply tsum_eq_sum
    intro j hj
    have h : (k:ℤ)-j < 0 ∨ (k:ℤ)+j < 0 := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hj
      omega
    rcases h with h | h
    · rw [choose_negative q n ((k:ℤ)-j) h, mul_zero, zero_mul]
    · rw [choose_negative q n ((k:ℤ)+j) h, mul_zero]
  rw [← hs]
  exact (value_eq_choose q hq hq0 n k).trans (choose_nat q n k)

end
end Borwein.CiglerIdentity
