import Borwein.DilogarithmUpper
import Borwein.ExpCertificate

set_option autoImplicit false

namespace Borwein.DilogarithmTail
noncomputable section
open DilogarithmUpper

def series (q : ℝ) : ℝ := ∑' k : ℕ, q^k/(k:ℝ)^2

theorem series_summable (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Summable (fun k : ℕ => q^k/(k:ℝ)^2) := by
  apply hasSum_zeta_two.summable.of_norm_bounded
  intro k
  rw [Real.norm_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right (pow_le_one₀ hq hq1) (sq_nonneg (k:ℝ))

theorem tail_bound (K : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    ‖∑' j : ℕ, q^(j+(K+1))/((j+(K+1):ℕ):ℝ)^2‖ ≤
      (q^(K+1)/((K+1:ℕ):ℝ)^2)*(1-q)⁻¹ := by
  apply tsum_of_norm_bounded ((hasSum_geometric_of_lt_one hq hq1).mul_left
    (q^(K+1)/((K+1:ℕ):ℝ)^2))
  intro j
  rw [Real.norm_of_nonneg (by positivity)]
  have hn : ((K+1:ℕ):ℝ) ≤ ((j+(K+1):ℕ):ℝ) := by exact_mod_cast Nat.le_add_left (K+1) j
  have hd : ((K+1:ℕ):ℝ)^2 ≤ ((j+(K+1):ℕ):ℝ)^2 := by nlinarith
  have h := div_le_div_of_nonneg_left (pow_nonneg hq (j+(K+1))) (by positivity : (0:ℝ) < ((K+1:ℕ):ℝ)^2) hd
  apply h.trans_eq
  rw [pow_add]
  ring

theorem series_upper (K : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    series q ≤ (∑ k ∈ Finset.range (K+1), q^k/(k:ℝ)^2)+
      (q^(K+1)/((K+1:ℕ):ℝ)^2)*(1-q)⁻¹ := by
  have he := (series_summable q hq hq1.le).sum_add_tsum_nat_add (K+1)
  change _ = series q at he
  rw [← he]
  apply add_le_add le_rfl
  exact (Real.le_norm_self _).trans (tail_bound K q hq hq1)

theorem radial_upper (τ q : ℝ) (hτ : 0 ≤ τ)
    (hq : Real.exp (-τ) ≤ q) (hq1 : q ≤ 1) : radial τ ≤ series q := by
  have hq0 : 0 ≤ q := (Real.exp_pos _).le.trans hq
  apply (radial_summable τ hτ).tsum_le_tsum _ (series_summable q hq0 hq1)
  intro k
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hq k) (sq_nonneg (k:ℝ))

theorem radial_half : radial (1/2) ≤ 369/500 := by
  have he : Real.exp (-(1/2:ℝ)) ≤ 3033/5000 := by
    apply (ExpCertificate.exp_enclosure _ 0 (3033/5000) 12 (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  apply (radial_upper (1/2) (3033/5000) (by norm_num) he (by norm_num)).trans
  apply (series_upper 10 (3033/5000) (by norm_num) (by norm_num)).trans
  norm_num [Finset.sum_range_succ]

theorem radial_one : radial 1 ≤ 41/100 := by
  have he : Real.exp (-(1:ℝ)) ≤ 46/125 := by
    apply (ExpCertificate.exp_enclosure _ 0 (46/125) 12 (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  apply (radial_upper 1 (46/125) (by norm_num) he (by norm_num)).trans
  apply (series_upper 10 (46/125) (by norm_num) (by norm_num)).trans
  norm_num [Finset.sum_range_succ]

end
end Borwein.DilogarithmTail
