import Borwein.RogersProductLimit
import Borwein.PeriodicEulerProduct

set_option autoImplicit false

namespace Borwein.RogersProducts
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerQBinomial EulerFiniteBinomial
  EulerFiniteTriple EulerGaussianLimit RogersProductLimit Filter
open scoped Topology

def residue (q : ℂ) (r : ℕ) : ℂ := infiniteProduct (q^5) (-q^r)

theorem residue_eq (q : ℂ) (j : Fin 4) :
    residue q (j.val+1)=PeriodicEulerProduct.residueEuler j q := by
  unfold residue infiniteProduct PeriodicEulerProduct.residueEuler
  apply tprod_congr
  intro n
  simp only [PeriodicEulerProduct.exponent, ← pow_mul, ← sub_eq_add_neg,
    show -(q^(j.val+1)) * q^(5*n)= -(q^(j.val+1)*q^(5*n)) by ring, ← pow_add]
  congr 2
  omega

theorem residue_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (r : ℕ) (hr : 0 < r) :
    residue q r ≠ 0 := by
  unfold residue infiniteProduct
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    have he : 1+(-q^r)*(q^5)^n=1-q^(5*n+r) := by
      rw [pow_add, pow_mul]
      ring
    rw [he]
    exact factor_ne_zero q hq _ (by omega)
  · have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
    simpa only [norm_mul, Complex.norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg (q^5)) hq5).mul_left ‖-q^r‖

theorem finite_euler_split (q : ℂ) (n : ℕ) :
    finiteEuler (5*n) q=finiteEuler n (q^5)*product (q^5) (-q) n*
      product (q^5) (-q^2) n*product (q^5) (-q^3) n*product (q^5) (-q^4) n := by
  induction n with
  | zero => simp [finiteEuler, product]
  | succ n ih =>
    have hs : finiteEuler (5*(n+1)) q=finiteEuler (5*n) q*
        ((1-q^(5*n+1))*(1-q^(5*n+2))*(1-q^(5*n+3))*(1-q^(5*n+4))*(1-q^(5*n+5))) := by
      rw [show 5*(n+1)=5*n+5 by omega]
      unfold finiteEuler
      rw [Finset.prod_range_add]
      norm_num [Finset.prod_range_succ]
    rw [hs, ih, pochhammer_succ]
    simp only [product_append, pow_add, pow_mul, pow_succ]
    ring

theorem euler_split (q : ℂ) (hq : ‖q‖ < 1) :
    euler q=euler (q^5)*residue q 1*residue q 2*residue q 3*residue q 4 := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  have hl := (finiteEuler_tendsto q hq).comp
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 5*n by omega) tendsto_id)
  have hr := ((((finiteEuler_tendsto (q^5) hq5).mul
    (product_limit (q^5) (-q) hq5)).mul (product_limit (q^5) (-q^2) hq5)).mul
    (product_limit (q^5) (-q^3) hq5)).mul (product_limit (q^5) (-q^4) hq5)
  have he : (fun n : ℕ => finiteEuler (5*n) q)=
      (fun n : ℕ => finiteEuler n (q^5)*product (q^5) (-q) n*
        product (q^5) (-q^2) n*product (q^5) (-q^3) n*product (q^5) (-q^4) n) :=
    funext (finite_euler_split q)
  change Tendsto (fun n : ℕ => finiteEuler (5*n) q) atTop (𝓝 (euler q)) at hl
  rw [he] at hl
  simpa only [residue, pow_one] using tendsto_nhds_unique hl hr

/-- The first analytic Rogers-Ramanujan product identity. -/
theorem first_identity (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' k : ℕ, RogersSeriesLimit.seriesTerm q 0 k)=(residue q 1*residue q 4)⁻¹ := by
  have hh := series_product_ratio q hq hq0 0 (by omega)
  have he : -(q^5)/q^2= -q^3 := by field_simp
  simp only [RogersProductFinite.offset, Nat.mul_zero, Nat.add_zero, he] at hh
  rw [hh, euler_split q hq]
  change (euler (q^5)*residue q 1*residue q 2*residue q 3*residue q 4)⁻¹*
    euler (q^5)*(residue q 2*residue q 3) = _
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  field_simp [euler_ne_zero (q^5) hq5, residue_ne_zero q hq 1 (by omega),
    residue_ne_zero q hq 2 (by omega), residue_ne_zero q hq 3 (by omega),
    residue_ne_zero q hq 4 (by omega)]

/-- The second analytic Rogers-Ramanujan product identity. -/
theorem second_identity (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' k : ℕ, RogersSeriesLimit.seriesTerm q 1 k)=(residue q 2*residue q 3)⁻¹ := by
  have hh := series_product_ratio q hq hq0 1 (by omega)
  have he : -(q^5)/q^4= -q := by field_simp
  norm_num only [RogersProductFinite.offset] at hh
  rw [he] at hh
  rw [hh, euler_split q hq]
  rw [show infiniteProduct (q^5) (-q)=residue q 1 by simp [residue]]
  change (euler (q^5)*residue q 1*residue q 2*residue q 3*residue q 4)⁻¹*
    euler (q^5)*(residue q 4*residue q 1) = _
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  field_simp [euler_ne_zero (q^5) hq5, residue_ne_zero q hq 1 (by omega),
    residue_ne_zero q hq 2 (by omega), residue_ne_zero q hq 3 (by omega),
    residue_ne_zero q hq 4 (by omega)]

end
end Borwein.RogersProducts
