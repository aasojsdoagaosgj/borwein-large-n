import Borwein.IntegerQBinomial
import Mathlib.Combinatorics.Enumerative.Pentagonal
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option autoImplicit false

namespace Borwein.CiglerWeights
noncomputable section
open Complex IntegerQBinomial

def weight (q : ℂ) (j : ℤ) : ℂ := (-1:ℂ)^j*q^(pentagonal j:ℤ)

theorem sign_neg (j : ℤ) : (-1:ℂ)^(-j)=(-1:ℂ)^j := by
  simp only [zpow_neg, ← inv_zpow, inv_neg, inv_one]

theorem sign_one_sub (j : ℤ) : (-1:ℂ)^(1-j)=-(-1:ℂ)^j := by
  rw [sub_eq_add_neg, zpow_add₀ (by norm_num), zpow_one, sign_neg]
  ring

theorem exponent_neg (j : ℤ) : (pentagonal (-j):ℤ)=(pentagonal j:ℤ)+j := by
  nlinarith [two_mul_natCast_pentagonal j, two_mul_natCast_pentagonal (-j)]

theorem exponent_one_sub (j : ℤ) :
    (pentagonal (1-j):ℤ)=(pentagonal j:ℤ)-2*j+1 := by
  nlinarith [two_mul_natCast_pentagonal j, two_mul_natCast_pentagonal (1-j)]

theorem weight_neg (q : ℂ) (hq : q ≠ 0) (j : ℤ) : weight q (-j)=weight q j*q^j := by
  rw [weight, weight, sign_neg, exponent_neg, zpow_add₀ hq]
  ring

theorem weight_one_sub (q : ℂ) (hq : q ≠ 0) (j : ℤ) :
    weight q (1-j)*q^(-(1-j))=-(weight q j*q^(-j)) := by
  unfold weight
  rw [sign_one_sub, mul_assoc, ← zpow_add₀ hq, exponent_one_sub]
  rw [show (pentagonal j:ℤ)-2*j+1+ -(1-j)=(pentagonal j:ℤ)+ -j by ring,
    zpow_add₀ hq]
  ring

theorem finite_support_summable (q : ℂ) (n : ℕ) (k : ℤ) (f : ℤ → ℂ) :
    Summable (fun j : ℤ => f j*choose q n (k-j)) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (k-(n:ℤ)) k)
  intro j hj
  have h : k-j < 0 ∨ (n:ℤ) < k-j := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hj
    omega
  rcases h with h | h
  · rw [choose_negative q n (k-j) h, mul_zero]
  · rw [choose_above q n (k-j) h, mul_zero]

theorem reflection_sum_zero (f : ℤ → ℂ) (hf : ∀ j, f (1-j)=-f j) :
    ∑' j : ℤ, f j = 0 := by
  let e : ℤ ≃ ℤ := {
    toFun := fun j => 1-j
    invFun := fun j => 1-j
    left_inv := by intro j; change 1-(1-j)=j; ring
    right_inv := by intro j; change 1-(1-j)=j; ring }
  have he := e.tsum_eq f
  have hh : (∑' j : ℤ, f (e j)) = -(∑' j : ℤ, f j) := by
    change (∑' j : ℤ, f (1-j)) = _
    simp only [hf, tsum_neg]
  rw [hh] at he
  have hr := congrArg Complex.re he
  have hi := congrArg Complex.im he
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im, Complex.neg_re, Complex.neg_im] at * <;> linarith

theorem cancellation (q : ℂ) (hq : q ≠ 0) (n : ℕ) (k : ℤ) :
    ∑' j : ℤ, weight q j*q^(-j)*choose q n (k-j)*choose q n (k+j-1) = 0 := by
  apply reflection_sum_zero
  intro j
  rw [weight_one_sub q hq j,
    show k-(1-j)=k+j-1 by ring, show k+(1-j)-1=k-j by ring]
  ring

end
end Borwein.CiglerWeights
