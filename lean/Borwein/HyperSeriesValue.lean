import Borwein.FormalSeriesValue
import Borwein.RogersSeriesLimit
import Borwein.RogersRamanujan
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false

namespace Borwein.HyperSeriesValue
noncomputable section
open Complex PowerSeries FormalSeriesValue EndpointEulerTail EulerQBinomial RogersSeriesLimit

theorem converges_qPochhammerInv (q : ℂ) (hq : ‖q‖ < 1) (j : ℕ) :
    Converges (qPochhammerInv j) q ((finiteEuler j q)⁻¹) := by
  induction j with
  | zero => simpa only [qPochhammerInv, Finset.range_zero, Finset.prod_empty,
      pochhammer_zero, inv_one] using converges_one q
  | succ j ih =>
    rw [qPochhammerInv_succ, pochhammer_succ]
    have hh := converges_mul ih (converges_qFactorInv q hq (j+1) (by omega))
    simpa only [mul_inv_rev, mul_comm] using hh

theorem converges_hyperTerm (q : ℂ) (hq : ‖q‖ < 1) (t j : ℕ) :
    Converges (hyperTerm t j) q (seriesTerm q (t-1) j) := by
  have hh := converges_mul (converges_X_pow q (hyperExponent t j))
    (converges_qPochhammerInv q hq j)
  simpa only [hyperTerm, hyperExponent, pow_two, seriesTerm, div_eq_mul_inv] using hh

theorem term_hyperSeries (q : ℂ) (t k : ℕ) :
    term (hyperSeries t) q k=∑' j : ℕ, term (hyperTerm t j) q k := by
  rw [tsum_eq_sum (s := Finset.range (k+1)) (fun j hj => by
    have hk : k < j := by simp only [Finset.mem_range] at hj; omega
    simp only [term, coeff_hyperTerm_eq_zero_of_lt_index hk, Int.cast_zero, zero_mul])]
  simp only [term, coeff_hyperSeries, Int.cast_sum, Finset.sum_mul]

theorem hyperTerm_norm_hasSum (q : ℂ) (hq : ‖q‖ < 1) (t j : ℕ) :
    HasSum (fun k : ℕ => ‖term (hyperTerm t j) q k‖) (seriesTerm (‖q‖:ℂ) (t-1) j).re := by
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  have hh := Complex.hasSum_re (converges_hyperTerm (‖q‖:ℂ) hr t j).2
  exact hh.congr_fun (fun k => nonneg_norm _ (coeffNonneg_hyperTerm t j) q k)

theorem double_norm_summable (q : ℂ) (hq : ‖q‖ < 1) (t : ℕ) :
    Summable (fun p : ℕ × ℕ => ‖term (hyperTerm t p.1) q p.2‖) := by
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  refine ⟨fun j => (hyperTerm_norm_hasSum q hq t j).summable, ?_⟩
  simp_rw [(hyperTerm_norm_hasSum q hq t _).tsum_eq]
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  exact (Complex.hasSum_re (series_summable (‖q‖:ℂ) hr (t-1)).hasSum).summable

theorem converges_hyperSeries (q : ℂ) (hq : ‖q‖ < 1) (t : ℕ) :
    Converges (hyperSeries t) q (∑' j : ℕ, seriesTerm q (t-1) j) := by
  have hn := double_norm_summable q hq t
  have hs := hn.of_norm
  have ha : Summable (fun k : ℕ => ‖term (hyperSeries t) q k‖) := by
    apply hn.prod_symm.prod.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    rw [term_hyperSeries]
    exact norm_tsum_le_tsum_norm (hn.prod_symm.prod_factor k)
  refine ⟨ha, ?_⟩
  have he : (∑' k : ℕ, term (hyperSeries t) q k)=∑' j : ℕ, seriesTerm q (t-1) j := by
    calc
      _ = ∑' k : ℕ, ∑' j : ℕ, term (hyperTerm t j) q k := tsum_congr (term_hyperSeries q t)
      _ = ∑' j : ℕ, ∑' k : ℕ, term (hyperTerm t j) q k :=
        Summable.tsum_comm (f := fun j k : ℕ => term (hyperTerm t j) q k) hs
      _ = _ := tsum_congr (fun j => (converges_hyperTerm q hq t j).2.tsum_eq)
  rw [← he]
  exact ha.of_norm.hasSum

theorem converges_rrSeries (q : ℂ) (hq : ‖q‖ < 1) (t : ℕ) (ht : 0 < t) :
    Converges (rrSeries t) q (∑' j : ℕ, seriesTerm q (t-1) j) := by
  rw [← hyperSeries_eq_rrSeries t ht]
  exact converges_hyperSeries q hq t

end
end Borwein.HyperSeriesValue
