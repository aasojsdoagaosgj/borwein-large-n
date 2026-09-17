import Borwein.EulerPentagonalLimit
import Borwein.EndpointCircleFunctions

set_option autoImplicit false

namespace Borwein.EulerWeakFilter
noncomputable section
open Complex FivePoleCircle EndpointEta EulerPentagonalCenter EulerPentagonalLimit

theorem zeta_nonzero : zeta ≠ 0 := by
  intro h
  have hh := zeta_primitive.pow_eq_one
  rw [h] at hh
  norm_num at hh

theorem rotated_norm (q : ℂ) (j : ℕ) : ‖zeta^j*q‖=‖q‖ := by
  rw [norm_mul, norm_pow, FiveRootProductExpansion.root_norm zeta zeta_primitive.pow_eq_one]
  simp

theorem monomial_weight (a p j : ℕ) :
    zeta^(-((a*j:ℕ):ℤ))*(zeta^j)^p=(zeta^((p:ℤ)-(a:ℤ)))^j := by
  rw [← pow_mul, ← zpow_natCast zeta (j*p), ← zpow_add₀ zeta_nonzero,
    ← zpow_natCast (zeta^((p:ℤ)-(a:ℤ))) j, ← zpow_mul]
  congr 1
  push_cast
  ring

theorem monomial_filter_zero (a p : ℕ) (ha : a=3 ∨ a=4)
    (hp : p%5=0 ∨ p%5=1 ∨ p%5=2) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*(zeta^j.val)^p)=0 := by
  let b : ℂ := zeta^((p:ℤ)-(a:ℤ))
  have hb : b ≠ 1 := by
    intro h
    have hd := (zeta_primitive.zpow_eq_one_iff_dvd ((p:ℤ)-(a:ℤ))).mp h
    have hm := Int.emod_eq_zero_of_dvd hd
    rcases ha with rfl|rfl <;> rcases hp with hp|hp|hp <;> omega
  have h5 : b^5=1 := by
    dsimp [b]
    rw [← zpow_natCast, ← zpow_mul]
    norm_num only [Nat.cast_ofNat]
    rw [
      show ((p:ℤ)-(a:ℤ))*(5:ℤ)=5*((p:ℤ)-(a:ℤ)) by ring,
      zpow_mul]
    change (zeta^(5:ℕ))^((p:ℤ)-(a:ℤ))=1
    rw [zeta_primitive.pow_eq_one, one_zpow]
  have hg := geom_sum_mul_neg b 5
  rw [h5, sub_self] at hg
  have hs : (∑ j ∈ Finset.range 5, b^j)=0 :=
    (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hb.symm)
  simp_rw [monomial_weight]
  convert hs using 1 <;> simp [Fin.sum_univ_succ, Finset.sum_range_succ, b] <;> ring

theorem atom_filter_zero (q : ℂ) (a : ℕ) (k : ℤ) (ha : a=3 ∨ a=4) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k)=0 := by
  have hp := EulerPentagonalFinite.pentagonal_residues k
  have he (j : Fin 5) : zeta^(-((a*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k=
      (zeta^(-((a*j.val:ℕ):ℤ))*(zeta^j.val)^(pentagonal k))*atom q k := by
    simp only [atom, mul_pow]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, monomial_filter_zero a (pentagonal k) ha hp, zero_mul]

theorem euler_filter_zero (q : ℂ) (a : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha : a=3 ∨ a=4) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*euler (zeta^j.val*q))=0 := by
  have hqj (j : Fin 5) : ‖zeta^j.val*q‖ < 1 := by rw [rotated_norm]; exact hq
  have hs (j : Fin 5) : Summable (fun k : ℤ => zeta^(-((a*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k) :=
    (atom_summable _ (hqj j)).mul_left _
  simp_rw [euler_pentagonal_nonzero _ (hqj _) (mul_ne_zero (pow_ne_zero _ zeta_nonzero) hq0),
    ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _ => hs j)]
  simp_rw [atom_filter_zero q a _ ha]
  exact tsum_zero

theorem G_filter_zero (q : ℂ) (a : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha : a=3 ∨ a=4) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*G (zeta^j.val*q))=0 := by
  have he (j : Fin 5) : (zeta^j.val*q)^5=q^5 := by
    have hp : (zeta^j.val)^5=(zeta^5)^j.val := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    rw [mul_pow, hp, zeta_primitive.pow_eq_one, one_pow, one_mul]
  simp_rw [G, he, ← mul_div_assoc]
  rw [← Finset.sum_div, euler_filter_zero q a hq hq0 ha, zero_div]

end
end Borwein.EulerWeakFilter
