import Borwein.EulerGaussianLimit
import Mathlib.Analysis.Normed.Group.Tannery

set_option autoImplicit false

namespace Borwein.EulerPentagonalCenter
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerQBinomial EulerFiniteBinomial EulerPentagonalFinite

def atom (q : ℂ) (j : ℤ) : ℂ := (-1:ℂ)^j*q^(pentagonal j)
def centerTerm (q : ℂ) (n k : ℕ) : ℂ := gaussian (q^3) (2*n) k*atom q ((k:ℤ)-(n:ℤ))

theorem twice_choose_two (n : ℕ) : 2*(n.choose 2:ℤ)=(n:ℤ)*((n:ℤ)-1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.choose_succ_succ']
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem exponent_identity (n k : ℕ) :
    3*(n+1).choose 2+3*k.choose 2+k=3*n*k+n+pentagonal ((k:ℤ)-(n:ℤ)) := by
  have h1 := twice_choose_two (n+1)
  have h2 := twice_choose_two k
  have h3 := two_mul_natCast_pentagonal ((k:ℤ)-(n:ℤ))
  push_cast at h1
  have he : 3*((n+1).choose 2:ℤ)+3*(k.choose 2:ℤ)+(k:ℤ)=
      3*(n:ℤ)*(k:ℤ)+(n:ℤ)+(pentagonal ((k:ℤ)-(n:ℤ)):ℤ) := by nlinarith
  exact_mod_cast he

theorem sign_shift (n k : ℕ) : (-1:ℂ)^n*(-1:ℂ)^((k:ℤ)-(n:ℤ))=(-1:ℂ)^k := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (by norm_num : (-1:ℂ) ≠ 0)]
  congr 1
  ring

theorem power_identity (q : ℂ) (n k : ℕ) (hq : q ≠ 0) :
    (q^3)^((n+1).choose 2)*(q^3)^(k.choose 2)*(-q/(q^3)^n)^k=
      (-q)^n*atom q ((k:ℤ)-(n:ℤ)) := by
  calc
    _ = (-1:ℂ)^k*(q^(3*(n+1).choose 2+3*k.choose 2+k)/q^(3*n*k)) := by
      rw [show -q=(-1:ℂ)*q by ring]
      simp only [pow_add, div_pow, mul_pow, ← pow_mul]
      ring
    _ = (-1:ℂ)^k*(q^n*q^(pentagonal ((k:ℤ)-(n:ℤ)))) := by
      rw [exponent_identity, pow_add, pow_add]
      field_simp
    _ = ((-1:ℂ)^n*(-1:ℂ)^((k:ℤ)-(n:ℤ)))*(q^n*q^(pentagonal ((k:ℤ)-(n:ℤ)))) := by
      rw [sign_shift]
    _ = _ := by
      unfold atom
      rw [show -q=(-1:ℂ)*q by ring, mul_pow]
      ring

theorem term_identity (q : ℂ) (n k : ℕ) (hq : q ≠ 0) :
    (q^3)^((n+1).choose 2)*term (q^3) (-q/(q^3)^n) (2*n) k=(-q)^n*centerTerm q n k := by
  unfold term centerTerm
  calc
    _ = gaussian (q^3) (2*n) k*((q^3)^((n+1).choose 2)*(q^3)^(k.choose 2)*(-q/(q^3)^n)^k) := by ring
    _ = _ := by rw [power_identity q n k hq]; ring

/-- The original finite Euler product with all powers already centered at k=n. -/
theorem finite_centered (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    finiteEuler (3*n) q=finiteEuler n (q^3)*(∑ k ∈ Finset.range (2*n+1), centerTerm q n k) := by
  apply mul_left_cancel₀ (pow_ne_zero n (neg_ne_zero.mpr hq0))
  rw [finite_euler_sum q n hq hq0]
  unfold expansion
  calc
    _ = finiteEuler n (q^3)*(∑ k ∈ Finset.range (2*n+1),
        (q^3)^((n+1).choose 2)*term (q^3) (-q/(q^3)^n) (2*n) k) := by
      rw [← Finset.mul_sum]
      ring
    _ = finiteEuler n (q^3)*(∑ k ∈ Finset.range (2*n+1), (-q)^n*centerTerm q n k) := by
      simp_rw [term_identity q n _ hq0]
    _ = _ := by rw [← Finset.mul_sum]; ring

end
end Borwein.EulerPentagonalCenter
