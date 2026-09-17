import Borwein.RogersThetaExponent
import Borwein.RogersGaussianLimit
import Borwein.BressoudIdentity

set_option autoImplicit false

namespace Borwein.RogersSeriesLimit
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerQBinomial EulerGaussianLimit
  RogersGaussianLimit RogersThetaExponent Filter
open scoped Topology

def seriesTerm (q : ℂ) (a k : ℕ) : ℂ := q^(k*k+a*k)/finiteEuler k q
def finiteTerm (q : ℂ) (a n k : ℕ) : ℂ := q^(k*k+a*k)*gaussian q n k
def finiteTheta (q : ℂ) (a n : ℕ) (j : ℤ) : ℂ :=
  thetaTerm q a j*IntegerQBinomial.choose q (2*n+a) ((n:ℤ)-2*j)

theorem power_bound (q : ℂ) (hq : ‖q‖ < 1) (a k : ℕ) :
    ‖q^(k*k+a*k)‖ ≤ ‖q‖^k := by
  rw [Complex.norm_pow]
  apply pow_le_pow_of_le_one (norm_nonneg q) hq.le
  by_cases hk : k=0
  · subst k; simp
  · have hk1 : 1 ≤ k := by omega
    nlinarith [Nat.zero_le (a*k)]

theorem finite_term_limit (q : ℂ) (hq : ‖q‖ < 1) (a k : ℕ) :
    Tendsto (fun n : ℕ => finiteTerm q a n k) atTop (𝓝 (seriesTerm q a k)) := by
  simpa only [finiteTerm, seriesTerm, div_eq_mul_inv] using
    (fixed_column q hq k).const_mul (q^(k*k+a*k))

theorem finite_term_bound (q : ℂ) (hq : ‖q‖ < 1) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n k : ℕ, ‖gaussian q n k‖ ≤ M) (a n k : ℕ) :
    ‖finiteTerm q a n k‖ ≤ M*‖q‖^k := by
  rw [finiteTerm, norm_mul]
  exact (mul_le_mul (power_bound q hq a k) (hb n k) (norm_nonneg _) (by positivity)).trans_eq (by ring)

theorem series_summable (q : ℂ) (hq : ‖q‖ < 1) (a : ℕ) :
    Summable (seriesTerm q a) := by
  obtain ⟨M,hM,hb⟩ := gaussian_bounded q hq
  apply ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left M).of_norm_bounded
  intro k
  exact le_of_tendsto (finite_term_limit q hq a k).norm
    (Eventually.of_forall (fun n => finite_term_bound q hq M hM.le hb a n k))

theorem sum_limit (q : ℂ) (hq : ‖q‖ < 1) (a : ℕ) :
    Tendsto (fun n : ℕ => ∑' k : ℕ, finiteTerm q a n k) atTop
      (𝓝 (∑' k : ℕ, seriesTerm q a k)) := by
  obtain ⟨M,hM,hb⟩ := gaussian_bounded q hq
  exact tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left M)
    (fun k => finite_term_limit q hq a k)
    (Eventually.of_forall (fun n k => finite_term_bound q hq M hM.le hb a n k))

theorem theta_term_limit (q : ℂ) (hq : ‖q‖ < 1) (a : ℕ) (j : ℤ) :
    Tendsto (fun n : ℕ => finiteTheta q a n j) atTop
      (𝓝 (thetaTerm q a j*(euler q)⁻¹)) :=
  (shifted_central q hq a j).const_mul (thetaTerm q a j)

theorem theta_term_bound (q : ℂ) (hq0 : q ≠ 0) (a : ℕ) (ha : a ≤ 1)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ n k : ℕ, ‖gaussian q n k‖ ≤ M)
    (n : ℕ) (j : ℤ) : ‖finiteTheta q a n j‖ ≤ M*‖q‖^(degree a j) := by
  rw [finiteTheta, norm_mul, term_norm q hq0 a ha j]
  exact (mul_le_mul_of_nonneg_left (integer_bound q M hM hb _ _) (by positivity)).trans_eq (by ring)

theorem theta_sum_limit (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a : ℕ) (ha : a ≤ 1) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, finiteTheta q a n j) atTop
      (𝓝 ((euler q)⁻¹*(∑' j : ℤ, thetaTerm q a j))) := by
  obtain ⟨M,hM,hb⟩ := gaussian_bounded q hq
  have hh := tendsto_tsum_of_dominated_convergence
    ((majorant_summable q hq a ha).mul_left M)
    (fun j => theta_term_limit q hq a j)
    (Eventually.of_forall (fun n j => theta_term_bound q hq0 a ha M hM.le hb n j))
  rw [tsum_mul_right, mul_comm] at hh
  exact hh

theorem finite_sum_eq (q : ℂ) (a n : ℕ) :
    (∑' k : ℕ, finiteTerm q a n k)=
      ∑ k ∈ Finset.range (n+1), q^(k*k+a*k)*gaussian q n k := by
  apply tsum_eq_sum
  intro k hk
  have hn : n < k := by
    simp only [Finset.mem_range] at hk
    omega
  rw [finiteTerm, gaussian_outside q n k hn, mul_zero]

/-- The analytic series/theta forms of both Rogers-Ramanujan identities. -/
theorem analytic_identity (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (a : ℕ) (ha : a ≤ 1) :
    (∑' k : ℕ, seriesTerm q a k)=(euler q)⁻¹*(∑' j : ℤ, thetaTerm q a j) := by
  have he : (fun n : ℕ => ∑' k : ℕ, finiteTerm q a n k)=
      (fun n : ℕ => ∑' j : ℤ, finiteTheta q a n j) := by
    funext n
    rw [finite_sum_eq]
    exact BressoudIdentity.finite_rogers_ramanujan q hq hq0 n a ha
  have hl := sum_limit q hq a
  rw [he] at hl
  exact tendsto_nhds_unique hl (theta_sum_limit q hq hq0 a ha)

end
end Borwein.RogersSeriesLimit
