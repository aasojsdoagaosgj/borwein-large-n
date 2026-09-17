import Borwein.EndpointTailGlobalKernel
import Borwein.EndpointWeakTail

set_option autoImplicit false

namespace Borwein.EndpointTailGlobalLog
noncomputable section
open Complex EndpointTailGlobalKernel

def radialX (n : ℕ) (v : ℝ) : ℝ := Real.exp (-((5*n:ℕ):ℝ)*v)

theorem majorant_hasSum (n : ℕ) (q : ℂ) (hn : 0 < n) (hq : ‖q‖ < 1) :
    HasSum (fun l : ℕ => (4/(1-‖q‖^5))*(‖q‖^(5*n))^(l+1))
      ((4/(1-‖q‖^5))*‖q‖^(5*n)/(1-‖q‖^(5*n))) := by
  have hr : ‖q‖^(5*n) < 1 := pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hg := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ ‖q‖^(5*n)) hr).mul_left
    ((4/(1-‖q‖^5))*‖q‖^(5*n))
  have he : ((4/(1-‖q‖^5))*‖q‖^(5*n))*(1-‖q‖^(5*n))⁻¹ =
      (4/(1-‖q‖^5))*‖q‖^(5*n)/(1-‖q‖^(5*n)) := by ring
  rw [he] at hg
  exact hg.congr_fun (fun l => by rw [pow_succ]; ring)

theorem log_bound (n : ℕ) (q : ℂ) (hn : 0 < n) (hq : ‖q‖ < 1) :
    ‖EndpointTailLog.tailLog n q‖ ≤ (4/(1-‖q‖^5))*‖q‖^(5*n)/(1-‖q‖^(5*n)) := by
  have hm := majorant_hasSum n q hn hq
  have hs : Summable (term n q) := hm.summable.of_norm_bounded (fun l => term_bound n l q hq)
  rw [EndpointTailFourier.tailLog_series n q hq]
  change ‖∑' l : ℕ, term n q l‖ ≤ _
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum (fun l => term_bound n l q hq) hm.summable).trans_eq hm.tsum_eq)

theorem inverse_exponential (u : ℝ) (hu : 0 < u) :
    1/(1-Real.exp (-u)) ≤ 1+1/u := by
  have he : 0 < Real.exp u-1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hu)
  have hden : 1-Real.exp (-u) ≠ 0 := ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hbase : u ≤ Real.exp u-1 := by linarith [Real.add_one_le_exp u]
  have hb := one_div_le_one_div_of_le hu hbase
  have hid : 1/(1-Real.exp (-u)) = 1+1/(Real.exp u-1) := by
    rw [Real.exp_neg]
    have hn := Real.exp_ne_zero u
    field_simp
    ring
  rw [hid]
  linarith

theorem radius_power (q : ℂ) (v : ℝ) (hq : ‖q‖=Real.exp (-v)) (k : ℕ) :
    ‖q‖^k = Real.exp (-(k:ℝ)*v) := by
  rw [hq, ← Real.exp_nat_mul]
  congr 1
  ring

theorem radialX_lt_one (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : radialX n v < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have hp : (0:ℝ) < ((5*n:ℕ):ℝ) := by positivity
  exact mul_neg_of_neg_of_pos (by linarith) hv

theorem radius_log_bound (n : ℕ) (q : ℂ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hq : ‖q‖=Real.exp (-v)) :
    ‖EndpointTailLog.tailLog n q‖ ≤ 4*(1+1/(5*v))*radialX n v/(1-radialX n v) := by
  have hq1 : ‖q‖ < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hb := log_bound n q hn hq1
  rw [radius_power q v hq 5, radius_power q v hq (5*n)] at hb
  change ‖EndpointTailLog.tailLog n q‖ ≤ 4/(1-Real.exp (-(5:ℝ)*v))*radialX n v/(1-radialX n v) at hb
  have he := inverse_exponential (5*v) (by positivity)
  have hC : 4/(1-Real.exp (-(5:ℝ)*v)) ≤ 4*(1+1/(5*v)) := by
    have h := mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 4)
    simpa only [neg_mul, mul_one_div] using h
  apply hb.trans
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le)
    (sub_nonneg.mpr (radialX_lt_one n v hn hv).le)

theorem endpoint_log_bound (n : ℕ) (q : ℂ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hq : ‖q‖=Real.exp (-v)) :
    ‖EndpointTailLog.tailLog n q‖ ≤ radialX n v/v := by
  have hr : radialX n v ≤ 1/100 := by
    have he := EndpointWeakTail.exponential_threshold.trans (Real.exp_le_exp.mpr hτ)
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<100) he
    simpa only [radialX, neg_mul, Real.exp_neg, one_div] using h
  have hd : 0 < 1-radialX n v := sub_pos.mpr (radialX_lt_one n v hn hv)
  have hrate : 4*(v+1/5)/(1-radialX n v) ≤ 1 := (div_le_iff₀ hd).mpr (by linarith)
  have he : 4*(1+1/(5*v))*radialX n v/(1-radialX n v) =
      (4*(v+1/5)/(1-radialX n v))*(radialX n v/v) := by field_simp
  apply (radius_log_bound n q v hn hv hq).trans
  rw [he]
  exact mul_le_of_le_one_left (div_nonneg (Real.exp_pos _).le hv.le) hrate

theorem exp_error_bound (z : ℂ) (B : ℝ) (hB : ‖z‖ ≤ B) : ‖exp z-1‖ ≤ B*Real.exp B := by
  have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp z 1
  simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one] at hb
  exact hb.trans (mul_le_mul hB (Real.exp_le_exp.mpr hB) (Real.exp_pos _).le ((norm_nonneg _).trans hB))

/-- Manuscript (5.10) on the entire circle; no angular restriction is imposed. -/
theorem endpoint_tail_bound (n : ℕ) (q : ℂ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hq : ‖q‖=Real.exp (-v)) :
    ‖EndpointFiniteConnection.tail n q-1‖ ≤ (radialX n v/v)*Real.exp (radialX n v/v) := by
  have hq1 : ‖q‖ < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  rw [← EndpointTailLog.exp_tailLog n q hq1]
  exact exp_error_bound _ _ (endpoint_log_bound n q v hn hv hV hτ hq)

end
end Borwein.EndpointTailGlobalLog
