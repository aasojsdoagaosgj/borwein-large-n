import Borwein.RogersSeriesLimit
import Borwein.EulerPentagonalCenter

set_option autoImplicit false

namespace Borwein.RogersProductFinite
noncomputable section
open Complex EulerQBinomial EulerFiniteBinomial EulerFiniteTriple
  EulerPentagonalCenter RogersThetaExponent

def offset (a : ℕ) : ℕ := 2+2*a
def centered (q : ℂ) (a n : ℕ) (j : ℤ) : ℂ :=
  IntegerQBinomial.choose (q^5) (2*n) ((n:ℤ)+j)*thetaTerm q a j

theorem exponent_identity (a n k : ℕ) (ha : a ≤ 1) :
    5*(n+1).choose 2+5*k.choose 2+offset a*k=
      5*n*k+offset a*n+degree a ((k:ℤ)-(n:ℤ)) := by
  have h1 := twice_choose_two (n+1)
  have h2 := twice_choose_two k
  have h3 := twice_exponent a ((k:ℤ)-(n:ℤ))
  rw [← degree_cast a ha] at h3
  push_cast at h1
  have he : 5*((n+1).choose 2:ℤ)+5*(k.choose 2:ℤ)+(offset a:ℤ)*(k:ℤ)=
      5*(n:ℤ)*(k:ℤ)+(offset a:ℤ)*(n:ℤ)+(degree a ((k:ℤ)-(n:ℤ)):ℤ) := by
    simp only [offset, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  exact_mod_cast he

theorem power_identity (q : ℂ) (hq0 : q ≠ 0) (a n k : ℕ) (ha : a ≤ 1) :
    (q^5)^((n+1).choose 2)*(q^5)^(k.choose 2)*(-q^(offset a)/(q^5)^n)^k=
      (-q^(offset a))^n*thetaTerm q a ((k:ℤ)-(n:ℤ)) := by
  calc
    _ = (-1:ℂ)^k*(q^(5*(n+1).choose 2+5*k.choose 2+offset a*k)/q^(5*n*k)) := by
      rw [show -q^(offset a)=(-1:ℂ)*q^(offset a) by ring]
      simp only [pow_add, div_pow, mul_pow, ← pow_mul]
      ring
    _ = (-1:ℂ)^k*(q^(offset a*n)*q^(degree a ((k:ℤ)-(n:ℤ)))) := by
      rw [exponent_identity a n k ha, pow_add, pow_add]
      field_simp
    _ = ((-1:ℂ)^n*(-1:ℂ)^((k:ℤ)-(n:ℤ)))*
        (q^(offset a*n)*q^(degree a ((k:ℤ)-(n:ℤ)))) := by
      rw [sign_shift]
    _ = _ := by
      rw [term_as_power q hq0 a ha, show -q^(offset a)=(-1:ℂ)*q^(offset a) by ring,
        mul_pow, ← pow_mul]
      ring

theorem term_identity (q : ℂ) (hq0 : q ≠ 0) (a n k : ℕ) (ha : a ≤ 1) :
    (q^5)^((n+1).choose 2)*term (q^5) (-q^(offset a)/(q^5)^n) (2*n) k=
      (-q^(offset a))^n*centered q a n ((k:ℤ)-(n:ℤ)) := by
  unfold term centered
  rw [show (n:ℤ)+((k:ℤ)-(n:ℤ))=(k:ℤ) by ring, IntegerQBinomial.choose_nat]
  calc
    _ = gaussian (q^5) (2*n) k*
        ((q^5)^((n+1).choose 2)*(q^5)^(k.choose 2)*(-q^(offset a)/(q^5)^n)^k) := by ring
    _ = _ := by rw [power_identity q hq0 a n k ha]; ring

theorem finite_centered (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a n : ℕ) (ha : a ≤ 1) :
    product (q^5) (-q^(offset a)) n*product (q^5) (-(q^5)/q^(offset a)) n=
      ∑ k ∈ Finset.range (2*n+1), centered q a n ((k:ℤ)-(n:ℤ)) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  apply mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr (pow_ne_zero _ hq0)))
  rw [← mul_assoc, ← finite_triple_sum (q^5) (q^(offset a)) n hq5
    (pow_ne_zero _ hq0) (pow_ne_zero _ hq0)]
  unfold expansion
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => term_identity q hq0 a n k ha)

theorem centered_outside (q : ℂ) (a n : ℕ) (j : ℤ)
    (hj : ¬ (-(n:ℤ) ≤ j ∧ j ≤ (n:ℤ))) : centered q a n j=0 := by
  unfold centered
  have hs : (n:ℤ)+j < 0 ∨ (2*n:ℕ) < (n:ℤ)+j := by push_cast; omega
  rcases hs with hs | hs
  · rw [IntegerQBinomial.choose_negative _ _ _ hs, zero_mul]
  · rw [IntegerQBinomial.choose_above _ _ _ hs, zero_mul]

theorem finite_reindex (q : ℂ) (a n : ℕ) :
    (∑ k ∈ Finset.range (2*n+1), centered q a n ((k:ℤ)-(n:ℤ)))=
      ∑' j : ℤ, centered q a n j := by
  rw [tsum_eq_sum (s := Finset.Icc (-(n:ℤ)) (n:ℤ))
    (fun j hj => centered_outside q a n j (by simpa only [Finset.mem_Icc] using hj))]
  apply Finset.sum_bij (fun (k : ℕ) _ => (k:ℤ)-(n:ℤ))
  · intro k hk
    have hkn := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr (by omega)
  · intro k hk l hl he
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨((n:ℤ)+j).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro k hk
    rfl

theorem finite_product_sum (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a n : ℕ) (ha : a ≤ 1) :
    product (q^5) (-q^(offset a)) n*product (q^5) (-(q^5)/q^(offset a)) n=
      ∑' j : ℤ, centered q a n j := by
  rw [finite_centered q hq hq0 a n ha, finite_reindex]

end
end Borwein.RogersProductFinite
