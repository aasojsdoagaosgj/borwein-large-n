import Borwein.EndpointTailLog
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

namespace Borwein.EndpointTailFourier
noncomputable section
open Complex EndpointTailLog

def term (N : ℕ) (q : ℂ) (j l : ℕ) : ℂ := q^((j+N+1)*(l+1))/((l+1:ℕ):ℂ)
def frequency (N : ℕ) (q : ℂ) (l : ℕ) : ℂ :=
  q^((N+1)*(l+1))/(((l+1:ℕ):ℂ)*(1-q^(l+1)))

theorem term_norm_bound (N j l : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖term N q j l‖ ≤ ‖q‖^(N+1)*‖q‖^j*‖q‖^l := by
  have he : j+N+1+l ≤ (j+N+1)*(l+1) := by nlinarith
  calc
    _ = ‖q‖^((j+N+1)*(l+1))/((l+1:ℕ):ℝ) := by simp only [term, norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ ‖q‖^((j+N+1)*(l+1)) := div_le_self (by positivity) (by exact_mod_cast Nat.le_add_left 1 l)
    _ ≤ ‖q‖^(j+N+1+l) := pow_le_pow_of_le_one (norm_nonneg _) hq.le he
    _ = _ := by simp only [pow_add, pow_one]; ring

theorem double_summable (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun p : ℕ×ℕ => term N q p.1 p.2) := by
  have hg := summable_geometric_of_lt_one (norm_nonneg q) hq
  have hb := (hg.mul_of_nonneg hg (fun j => by positivity) (fun l => by positivity)).mul_left (‖q‖^(N+1))
  apply hb.of_norm_bounded
  intro p
  simpa only [mul_assoc] using term_norm_bound N p.1 p.2 q hq

theorem row_hasSum (N j : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (term N q j) (-log (1-q^(j+N+1))) := by
  have hn : ‖q^(j+N+1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have he := (hasSum_nat_add_iff' 1).mpr (Complex.hasSum_taylorSeries_neg_log hn)
  unfold term
  simpa [← pow_mul] using he

theorem column_hasSum (N l : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun j : ℕ => term N q j l) (frequency N q l) := by
  have hn : ‖q^(l+1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have he := (hasSum_geometric_of_norm_lt_one hn).mul_left (q^((N+1)*(l+1))/((l+1:ℕ):ℂ))
  have hf : (fun j : ℕ => term N q j l) =
      (fun j : ℕ => (q^((N+1)*(l+1))/((l+1:ℕ):ℂ))*(q^(l+1))^j) := by
    funext j
    unfold term
    rw [show (j+N+1)*(l+1) = (N+1)*(l+1)+(l+1)*j by ring, pow_add, pow_mul]
    ring
  have ha : frequency N q l = (q^((N+1)*(l+1))/((l+1:ℕ):ℂ))*(1-q^(l+1))⁻¹ := by
    simp only [frequency, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hf, ha]
  exact he

theorem frequency_summable (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (frequency N q) := by
  have he := (double_summable N q hq).prod_symm.prod
  exact he.congr (fun l => (column_hasSum N l q hq).tsum_eq)

/-- Absolute convergence justifies exchanging factor and frequency sums. -/
theorem inverseLog_series (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    inverseLog N q = ∑' l : ℕ, frequency N q l := by
  unfold inverseLog
  rw [← tsum_neg]
  calc
    _ = ∑' j : ℕ, ∑' l : ℕ, term N q j l :=
      tsum_congr (fun j => (row_hasSum N j q hq).tsum_eq.symm)
    _ = ∑' l : ℕ, ∑' j : ℕ, term N q j l := (double_summable N q hq).tsum_comm.symm
    _ = _ := tsum_congr (fun l => (column_hasSum N l q hq).tsum_eq)

theorem tailLog_series (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    tailLog n q = ∑' l : ℕ, (frequency (5*n) q l-frequency n (q^5) l) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  rw [tailLog, inverseLog_series _ q hq, inverseLog_series _ (q^5) hq5,
    (frequency_summable (5*n) q hq).tsum_sub (frequency_summable n (q^5) hq5)]

end
end Borwein.EndpointTailFourier
