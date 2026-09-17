import Borwein.PentagonalMiddle
import Borwein.EulerWeakFilter
import Borwein.RogersFormalProducts
import Borwein.FormalSeriesOperations

set_option autoImplicit false

namespace Borwein.FifthRootMiddle
noncomputable section
open Complex FivePoleCircle EndpointEta EulerWeakFilter EulerPentagonalCenter
  EulerPentagonalLimit FormalSeriesValue FormalSeriesOperations

theorem monomial_filter (a p : ℕ) :
    (∑ j : Fin 5, zeta^(-((a*j.val:ℕ):ℤ))*(zeta^j.val)^p)=
      if p%5=a%5 then (5:ℂ) else 0 := by
  let b : ℂ := zeta^((p:ℤ)-(a:ℤ))
  simp_rw [monomial_weight]
  change (∑ j : Fin 5, b^j.val)=_
  by_cases hpa : p%5=a%5
  · have hd : (5:ℤ) ∣ (p:ℤ)-(a:ℤ) := by omega
    have hb : b=1 := (zeta_primitive.zpow_eq_one_iff_dvd _).mpr hd
    simp [hb,hpa]
  · have hb : b ≠ 1 := by
      intro he
      have hd := (zeta_primitive.zpow_eq_one_iff_dvd ((p:ℤ)-(a:ℤ))).mp he
      have hm := Int.emod_eq_zero_of_dvd hd
      omega
    have h5 : b^5=1 := by
      dsimp [b]
      rw [← zpow_natCast, ← zpow_mul]
      norm_num only [Nat.cast_ofNat]
      rw [show ((p:ℤ)-(a:ℤ))*(5:ℤ)=5*((p:ℤ)-(a:ℤ)) by ring, zpow_mul]
      change (zeta^(5:ℕ))^((p:ℤ)-(a:ℤ))=1
      rw [zeta_primitive.pow_eq_one, one_zpow]
    have hg := geom_sum_mul_neg b 5
    rw [h5, sub_self] at hg
    have hs : (∑ j ∈ Finset.range 5, b^j)=0 :=
      (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hb.symm)
    rw [if_neg hpa]
    convert hs using 1 <;> simp [Fin.sum_univ_succ, Finset.sum_range_succ] <;> ring

theorem atom_filter (q : ℂ) (k : ℤ) :
    (∑ j : Fin 5, zeta^(-((1*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k)=
      5*PentagonalMiddle.filtered q k := by
  have he (j : Fin 5) : zeta^(-((1*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k=
      (zeta^(-((1*j.val:ℕ):ℤ))*(zeta^j.val)^(pentagonal k))*atom q k := by
    simp only [atom, mul_pow]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul, monomial_filter]
  norm_num only [Nat.one_mod]
  unfold PentagonalMiddle.filtered
  split_ifs <;> ring

theorem euler_middle_filter (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑ j : Fin 5, zeta^(-((1*j.val:ℕ):ℤ))*euler (zeta^j.val*q))=
      -5*q*euler (q^25) := by
  have hqj (j : Fin 5) : ‖zeta^j.val*q‖ < 1 := by rw [rotated_norm]; exact hq
  have hs (j : Fin 5) : Summable (fun k : ℤ => zeta^(-((1*j.val:ℕ):ℤ))*atom (zeta^j.val*q) k) :=
    (atom_summable _ (hqj j)).mul_left _
  simp_rw [euler_pentagonal_nonzero _ (hqj _) (mul_ne_zero (pow_ne_zero _ zeta_nonzero) hq0),
    ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun j _ => hs j)]
  simp_rw [atom_filter]
  rw [tsum_mul_left, PentagonalMiddle.filtered_sum q hq hq0]
  ring

theorem G_middle_filter (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑ j : Fin 5, zeta^(-((1*j.val:ℕ):ℤ))*G (zeta^j.val*q))=
      -5*q*(euler (q^25)/euler (q^5)) := by
  have he (j : Fin 5) : (zeta^j.val*q)^5=q^5 := by
    have hp : (zeta^j.val)^5=(zeta^5)^j.val := by
      simp only [← pow_mul]
      rw [Nat.mul_comm]
    rw [mul_pow, hp, zeta_primitive.pow_eq_one, one_pow, one_mul]
  simp_rw [G, he, ← mul_div_assoc]
  rw [← Finset.sum_div, euler_middle_filter q hq hq0]

theorem middle_series_value (q : ℂ) (hq : ‖q‖ < 1) :
    Converges (PowerSeries.X*PowerSeries.expand 5 (by omega) (rrSeries 1*rrSeries 2))
      q (q*(euler (q^25)/euler (q^5))) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hh := converges_mul (converges_X_pow q 1)
    (converges_expand 5 (by omega) (RogersFormalProducts.product_value (q^5) hq5))
  simpa only [pow_one, ← pow_mul, show 5*5=25 by omega] using hh

end
end Borwein.FifthRootMiddle
