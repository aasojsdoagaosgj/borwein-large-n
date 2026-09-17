import Borwein.WatsonPochhammer
import Borwein.RogersProductLimit

set_option autoImplicit false

namespace Borwein.WatsonPochhammerLimit
noncomputable section
open Complex EndpointEta EulerGaussianLimit RogersProductLimit WatsonPochhammer Filter
open scoped Topology

def limit (q a : ℂ) : ℂ := euler q * infiniteProduct q (-a)

theorem product_ne_zero (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) : infiniteProduct q (-a) ≠ 0 := by
  unfold infiniteProduct
  apply tprod_one_add_ne_zero_of_summable
  · intro j
    simpa only [neg_mul, sub_eq_add_neg] using hA j
  · simpa only [norm_mul, Complex.norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖-a‖

theorem limit_ne_zero (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) : limit q a ≠ 0 :=
  mul_ne_zero (euler_ne_zero q hq) (product_ne_zero q a hq hA)

theorem paired_tendsto (q a : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (paired q a) atTop (𝓝 (limit q a)) :=
  (finiteEuler_tendsto q hq).mul (product_limit q (-a) hq)

theorem inverse_nat_tendsto (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) :
    Tendsto (fun n : ℕ => (paired q a n)⁻¹) atTop (𝓝 ((limit q a)⁻¹)) :=
  (paired_tendsto q a hq).inv₀ (limit_ne_zero q a hq hA)

theorem inverse_bounded (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ k : ℤ, ‖inverse q a k‖ ≤ M := by
  obtain ⟨M,hM,hb⟩ := (Metric.isBounded_range_of_tendsto _
    (inverse_nat_tendsto q a hq hA)).exists_pos_norm_le
  refine ⟨M,hM,fun k => ?_⟩
  by_cases hk : 0 ≤ k
  · simp only [inverse, if_pos hk]
    exact hb _ ⟨k.toNat,rfl⟩
  · simp only [inverse, if_neg hk, norm_zero]
    exact hM.le

theorem shifted_index_tendsto (k : ℤ) :
    Tendsto (fun n : ℕ => ((n:ℤ)+k).toNat) atTop atTop := by
  have hk : -(k.natAbs:ℤ) ≤ k := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le k
  exact tendsto_atTop_mono (fun n : ℕ => show n-k.natAbs ≤ ((n:ℤ)+k).toNat by omega)
    (tendsto_sub_atTop_nat k.natAbs)

theorem inverse_shifted_tendsto (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) (k : ℤ) :
    Tendsto (fun n : ℕ => inverse q a ((n:ℤ)+k)) atTop (𝓝 ((limit q a)⁻¹)) := by
  have hh := (inverse_nat_tendsto q a hq hA).comp (shifted_index_tendsto k)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop k.natAbs] with n hn
  have hk : -(k.natAbs:ℤ) ≤ k := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le k
  simp only [Function.comp_def, inverse, if_pos (show 0 ≤ (n:ℤ)+k by omega)]

end
end Borwein.WatsonPochhammerLimit
