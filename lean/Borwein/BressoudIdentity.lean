import Borwein.BressoudConvolution

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Borwein.BressoudIdentity
noncomputable section
open Complex IntegerQBinomial IntegerQVandermonde CiglerWeights BressoudConvolution

def term (q : ℂ) (n a : ℕ) (k j : ℤ) : ℂ :=
  q^(k*k+(a:ℤ)*k)*weight q j*q^((a:ℤ)*j)*
    choose q n (k-j)*choose q (n+a) (k+j+(a:ℤ))

theorem double_summable (q : ℂ) (n a : ℕ) (ha : a ≤ 1) :
    Summable (fun p : ℤ × ℤ => term q n a p.1 p.2) := by
  apply summable_of_ne_finset_zero
    (s := (Finset.Icc (0:ℤ) (n:ℤ)).product (Finset.Icc (-(n:ℤ)-1) ((n:ℤ)+1)))
  intro p hp
  by_cases h1 : choose q n (p.1-p.2)=0
  · simp only [term, h1, mul_zero, zero_mul]
  by_cases h2 : choose q (n+a) (p.1+p.2+(a:ℤ))=0
  · simp only [term, h2, mul_zero]
  have hb1 := choose_range q n (p.1-p.2) h1
  have hb2 := choose_range q (n+a) (p.1+p.2+(a:ℤ)) h2
  have ha' : (a:ℤ) ≤ 1 := by exact_mod_cast ha
  push_cast at hb2
  exfalso
  apply hp
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
  omega

theorem regroup_term (q : ℂ) (hq0 : q ≠ 0) (n a : ℕ) (k j : ℤ) :
    term q n a k j = (weight q j*q^(j*j+2*(a:ℤ)*j))*
      (q^((k-j)*(k+j+(a:ℤ)))*choose q n (k-j)*choose q (n+a) (k+j+(a:ℤ))) := by
  have he : q^(k*k+(a:ℤ)*k)*q^((a:ℤ)*j) =
      q^(j*j+2*(a:ℤ)*j)*q^((k-j)*(k+j+(a:ℤ))) := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0]
    congr 1
    ring
  unfold term
  linear_combination (weight q j*choose q n (k-j)*choose q (n+a) (k+j+(a:ℤ)))*he

theorem bilateral_identity (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (n a : ℕ) (ha : a ≤ 1) :
    (∑' k : ℤ, q^(k*k+(a:ℤ)*k)*choose q n k) =
      ∑' j : ℤ, weight q j*q^(j*j+2*(a:ℤ)*j)*choose q (2*n+a) ((n:ℤ)-2*j) := by
  calc
    _ = ∑' k : ℤ, ∑' j : ℤ, term q n a k j := by
      apply tsum_congr
      intro k
      rw [← alternating_pair q hq hq0 n a ha k, ← tsum_mul_left]
      apply tsum_congr
      intro j
      unfold term
      ring
    _ = ∑' j : ℤ, ∑' k : ℤ, term q n a k j :=
      (Summable.tsum_comm (f := fun k j : ℤ => term q n a k j) (double_summable q n a ha)).symm
    _ = _ := by
      apply tsum_congr
      intro j
      simp_rw [regroup_term q hq0 n a]
      rw [tsum_mul_left, twisted_vandermonde q hq hq0 n a j]

theorem natural_sum (q : ℂ) (n a : ℕ) :
    (∑ k ∈ Finset.range (n+1), q^(k*k+a*k)*EulerQBinomial.gaussian q n k) =
      ∑' k : ℤ, q^(k*k+(a:ℤ)*k)*choose q n k := by
  have he : (∑' k : ℤ, q^(k*k+(a:ℤ)*k)*choose q n k) =
      ∑ k ∈ Finset.Icc (0:ℤ) (n:ℤ), q^(k*k+(a:ℤ)*k)*choose q n k := by
    apply tsum_eq_sum
    intro k hk
    have h : k < 0 ∨ (n:ℤ) < k := by simpa only [Finset.mem_Icc, not_and_or, not_le] using hk
    rcases h with h | h
    · rw [choose_negative q n k h, mul_zero]
    · rw [choose_above q n k h, mul_zero]
  rw [he]
  apply Finset.sum_bij (fun (k : ℕ) _ => (k:ℤ))
  · intro k hk
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc]
    omega
  · intro k hk l hl he
    exact_mod_cast he
  · intro k hk
    refine ⟨k.toNat, ?_, ?_⟩
    · simp only [Finset.mem_Icc] at hk
      simp only [Finset.mem_range]
      omega
    · simp only [Finset.mem_Icc] at hk
      omega
  · intro k _
    rw [choose_nat]
    have hp : (k:ℤ)*(k:ℤ)+(a:ℤ)*(k:ℤ)=((k*k+a*k:ℕ):ℤ) := by push_cast; rfl
    rw [hp, zpow_natCast]

theorem finite_rogers_ramanujan (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (n a : ℕ) (ha : a ≤ 1) :
    (∑ k ∈ Finset.range (n+1), q^(k*k+a*k)*EulerQBinomial.gaussian q n k) =
      ∑' j : ℤ, weight q j*q^(j*j+2*(a:ℤ)*j)*choose q (2*n+a) ((n:ℤ)-2*j) := by
  rw [natural_sum]
  exact bilateral_identity q hq hq0 n a ha

end
end Borwein.BressoudIdentity
