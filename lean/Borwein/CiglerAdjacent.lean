import Borwein.CiglerWeights

set_option autoImplicit false

namespace Borwein.CiglerAdjacent
noncomputable section
open Complex IntegerQBinomial CiglerWeights

def value (q : ℂ) (n : ℕ) (k : ℤ) : ℂ :=
  ∑' j : ℤ, weight q j*choose q n (k-j)*choose q n (k+j)

theorem product_summable (q : ℂ) (n m : ℕ) (k l : ℤ) (f : ℤ → ℂ) :
    Summable (fun j : ℤ => f j*choose q n (k-j)*choose q m (l+j)) := by
  apply (finite_support_summable q n k (fun j => f j*choose q m (l+j))).congr
  intro j
  ring

theorem neg_reindex (f : ℤ → ℂ) : (∑' j : ℤ, f (-j)) = ∑' j : ℤ, f j := by
  let e : ℤ ≃ ℤ := {
    toFun := fun j => -j
    invFun := fun j => -j
    left_inv := by intro j; change -(-j)=j; ring
    right_inv := by intro j; change -(-j)=j; ring }
  exact e.tsum_eq f

theorem reflected_value (q : ℂ) (hq : q ≠ 0) (n : ℕ) (k : ℤ) :
    (∑' j : ℤ, weight q j*q^j*choose q n (k-j)*choose q n (k+j)) = value q n k := by
  unfold value
  calc
    _ = ∑' j : ℤ, weight q (-j)*choose q n (k-(-j))*choose q n (k+(-j)) := by
      apply tsum_congr
      intro j
      rw [weight_neg q hq j, show k-(-j)=k+j by ring, show k+(-j)=k-j by ring]
      ring
    _ = _ := neg_reindex (fun j : ℤ => weight q j*choose q n (k-j)*choose q n (k+j))

theorem cancellation_plus (q : ℂ) (hq : q ≠ 0) (n : ℕ) (k : ℤ) :
    (∑' j : ℤ, weight q j*q^j*q^j*choose q n (k-j)*choose q n (k+j+1)) = 0 := by
  have he := cancellation q hq n (k+1)
  rw [← neg_reindex] at he
  convert he using 1
  apply tsum_congr
  intro j
  rw [weight_neg q hq j]
  simp only [neg_neg, sub_neg_eq_add]
  rw [show k+1+ -j-1=k-j by ring, show k+1+j=k+j+1 by ring]
  ring

theorem adjacent_right (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n : ℕ) (k : ℤ) :
    (∑' j : ℤ, weight q j*choose q n (k-j)*choose q (n+1) (k+j)) = value q n k := by
  have ht (j : ℤ) : weight q j*choose q n (k-j)*choose q (n+1) (k+j) =
      weight q j*choose q n (k-j)*choose q n (k+j)+
      q^((n:ℤ)+1-k)*(weight q j*q^(-j)*choose q n (k-j)*choose q n (k+j-1)) := by
    rw [pascal_right q n (k+j) hq,
      show (n:ℤ)+1-(k+j)=((n:ℤ)+1-k)+ -j by ring, zpow_add₀ hq0]
    ring
  have hs := product_summable q n n k (k-1) (fun j => weight q j*q^(-j))
  have hs' : Summable (fun j : ℤ => weight q j*q^(-j)*choose q n (k-j)*choose q n (k+j-1)) := by
    convert hs using 1
    ext j
    rw [show k-1+j=k+j-1 by ring]
  simp_rw [ht]
  rw [Summable.tsum_add (product_summable q n n k k (weight q)) (hs'.mul_left _),
    tsum_mul_left, cancellation q hq0 n k, mul_zero, add_zero]
  rfl

theorem adjacent_shift (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (n : ℕ) (k : ℤ) :
    (∑' j : ℤ, weight q j*q^j*choose q n (k-j)*choose q (n+1) (k+j+1)) = value q n k := by
  have ht (j : ℤ) : weight q j*q^j*choose q n (k-j)*choose q (n+1) (k+j+1) =
      weight q j*q^j*choose q n (k-j)*choose q n (k+j)+
      q^(k+1)*(weight q j*q^j*q^j*choose q n (k-j)*choose q n (k+j+1)) := by
    rw [pascal_left q n (k+j+1) hq, show k+j+1-1=k+j by ring,
      show k+j+1=(k+1)+j by ring, zpow_add₀ hq0]
    ring
  have hs := product_summable q n n k (k+1) (fun j => weight q j*q^j*q^j)
  have hs' : Summable (fun j : ℤ => weight q j*q^j*q^j*choose q n (k-j)*choose q n (k+j+1)) := by
    convert hs using 1
    ext j
    rw [show k+1+j=k+j+1 by ring]
  simp_rw [ht]
  rw [Summable.tsum_add (product_summable q n n k k (fun j => weight q j*q^j)) (hs'.mul_left _),
    tsum_mul_left, cancellation_plus q hq0 n k, mul_zero, add_zero]
  exact reflected_value q hq0 n k

end
end Borwein.CiglerAdjacent
