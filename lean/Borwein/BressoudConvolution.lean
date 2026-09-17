import Borwein.IntegerQVandermonde
import Borwein.CiglerIdentity

set_option autoImplicit false

namespace Borwein.BressoudConvolution
noncomputable section
open Complex IntegerQBinomial IntegerQVandermonde CiglerWeights CiglerAdjacent CiglerIdentity

theorem choose_range (q : ℂ) (n : ℕ) (k : ℤ) (hk : choose q n k ≠ 0) :
    0 ≤ k ∧ k ≤ (n:ℤ) := by
  constructor
  · by_contra h; exact hk (choose_negative q n k (by omega))
  · by_contra h; exact hk (choose_above q n k (by omega))

theorem choose_reflect (q : ℂ) (n : ℕ) (k : ℤ) :
    choose q n ((n:ℤ)-k) = choose q n k := by
  by_cases hk0 : k < 0
  · rw [choose_negative q n k hk0, choose_above q n ((n:ℤ)-k) (by omega)]
  by_cases hkn : (n:ℤ) < k
  · rw [choose_above q n k hkn, choose_negative q n ((n:ℤ)-k) (by omega)]
  have hk : 0 ≤ k := by omega
  have hkn' : k.toNat ≤ n := by omega
  rw [show k=(k.toNat:ℤ) by omega,
    show (n:ℤ)-(k.toNat:ℤ)=(n-k.toNat:ℕ) by omega, choose_nat, choose_nat]
  exact EulerQBinomial.gaussian_symmetry q n k.toNat hkn'

theorem reflection_reindex (c : ℤ) (f : ℤ → ℂ) :
    (∑' j : ℤ, f (c-j)) = ∑' j : ℤ, f j := by
  let e : ℤ ≃ ℤ := {
    toFun := fun j => c-j
    invFun := fun j => c-j
    left_inv := by intro j; change c-(c-j)=j; ring
    right_inv := by intro j; change c-(c-j)=j; ring }
  exact e.tsum_eq f

theorem twisted_vandermonde (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (n a : ℕ) (j : ℤ) :
    (∑' k : ℤ, q^((k-j)*(k+j+(a:ℤ)))*choose q n (k-j)*choose q (n+a) (k+j+(a:ℤ))) =
      choose q (2*n+a) ((n:ℤ)-2*j) := by
  have he := vandermonde q hq hq0 (n+a) n ((n:ℤ)-2*j)
  rw [convolution, ← reflection_reindex ((n:ℤ)-j)] at he
  have ht (k : ℤ) : q^((((n+a:ℕ):ℤ)-((n:ℤ)-j-k))*((n:ℤ)-2*j-((n:ℤ)-j-k)))*
      choose q (n+a) ((n:ℤ)-j-k)*choose q n ((n:ℤ)-2*j-((n:ℤ)-j-k)) =
      q^((k-j)*(k+j+(a:ℤ)))*choose q n (k-j)*choose q (n+a) (k+j+(a:ℤ)) := by
    have h1 : ((n+a:ℕ):ℤ)-((n:ℤ)-j-k)=k+j+(a:ℤ) := by push_cast; ring
    have h2 : (n:ℤ)-2*j-((n:ℤ)-j-k)=k-j := by ring
    have h3 : (n:ℤ)-j-k=((n+a:ℕ):ℤ)-(k+j+(a:ℤ)) := by push_cast; ring
    rw [h1, h2, h3, choose_reflect]
    rw [mul_comm (k+j+(a:ℤ)) (k-j)]
    ring
  simp_rw [ht] at he
  simpa only [show n+a+n=2*n+a by omega] using he

theorem alternating_pair (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (n a : ℕ) (ha : a ≤ 1) (k : ℤ) :
    (∑' j : ℤ, weight q j*q^((a:ℤ)*j)*choose q n (k-j)*choose q (n+a) (k+j+(a:ℤ))) =
      choose q n k := by
  have ha' : a=0 ∨ a=1 := by omega
  rcases ha' with rfl | rfl
  · simpa [value] using value_eq_choose q hq hq0 n k
  · have he := adjacent_shift q hq hq0 n k
    rw [value_eq_choose q hq hq0 n k] at he
    simpa using he

end
end Borwein.BressoudConvolution
