import Borwein.EulerPentagonalReindex

set_option autoImplicit false

namespace Borwein.EulerPentagonalLimit
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerQBinomial EulerGaussianLimit
  EulerPentagonalCenter EulerPentagonalReindex Filter
open scoped Topology

theorem atom_norm (q : ℂ) (j : ℤ) : ‖atom q j‖=‖q‖^(pentagonal j) := by
  simp [atom, norm_mul, norm_zpow, norm_pow]

theorem pentagonal_majorant_summable (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun j : ℤ => ‖q‖^(pentagonal j)) := by
  simpa only [Function.comp_def] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).comp_injective pentagonal_injective

theorem atom_summable (q : ℂ) (hq : ‖q‖ < 1) : Summable (atom q) :=
  (pentagonal_majorant_summable q hq).of_norm_bounded (fun j => (atom_norm q j).le)

theorem shifted_gaussian_limit (q : ℂ) (j : ℤ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => gaussian q (2*n) ((n:ℤ)+j).toNat) atTop (𝓝 ((euler q)⁻¹)) := by
  rcases j with k | k
  · convert central_positive q k hq using 1
    ext n
    congr 1 <;> omega
  · have he : ∀ n : ℕ, ((n:ℤ)+Int.negSucc k).toNat=n-(k+1) := by intro n; omega
    simp_rw [he]
    exact central_negative q (k+1) hq

theorem centered_limit (q : ℂ) (j : ℤ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => centered q n j) atTop (𝓝 ((euler (q^3))⁻¹*atom q j)) := by
  have hq3 : ‖q^3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hh := (shifted_gaussian_limit (q^3) j hq3).mul_const (atom q j)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop j.natAbs] with n hn
  have hj : -(n:ℤ) ≤ j ∧ j ≤ (n:ℤ) := by
    have habs : (j.natAbs:ℤ) ≤ (n:ℤ) := by exact_mod_cast hn
    rw [Int.natCast_natAbs] at habs
    exact abs_le.mp habs
  exact (centered_inside q n j hj).symm

theorem centered_bound (q : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n k : ℕ, ‖gaussian (q^3) n k‖ ≤ M) (n : ℕ) (j : ℤ) :
    ‖centered q n j‖ ≤ M*‖q‖^(pentagonal j) := by
  by_cases hj : -(n:ℤ) ≤ j ∧ j ≤ (n:ℤ)
  · rw [centered_inside q n j hj, norm_mul, atom_norm]
    exact mul_le_mul_of_nonneg_right (hb _ _) (by positivity)
  · rw [centered_outside q n j hj, norm_zero]
    positivity

theorem tsum_centered_limit (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => ∑' j : ℤ, centered q n j) atTop
      (𝓝 ((euler (q^3))⁻¹*(∑' j : ℤ, atom q j))) := by
  have hq3 : ‖q^3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  obtain ⟨M,hM,hb⟩ := gaussian_bounded (q^3) hq3
  have hh := tendsto_tsum_of_dominated_convergence
    ((pentagonal_majorant_summable q hq).mul_left M) (fun j => centered_limit q j hq)
    (Eventually.of_forall (fun n j => centered_bound q M hM.le hb n j))
  simpa only [tsum_mul_left] using hh

/-- Euler's pentagonal-number identity for every nonzero point of the open unit disk. -/
theorem euler_pentagonal_nonzero (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    euler q=∑' j : ℤ, atom q j := by
  have hq3 : ‖q^3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hl := (finiteEuler_tendsto q hq).comp
    (tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n : ℕ, n ≤ 3*n) tendsto_id)
  have hr := (finiteEuler_tendsto (q^3) hq3).mul (tsum_centered_limit q hq)
  have he : (fun n : ℕ => finiteEuler (3*n) q)=
      (fun n : ℕ => finiteEuler n (q^3)*(∑' j : ℤ, centered q n j)) :=
    funext (fun n => finite_euler_tsum q n hq hq0)
  change Tendsto (fun n : ℕ => finiteEuler (3*n) q) atTop (𝓝 (euler q)) at hl
  rw [he] at hl
  have hh := tendsto_nhds_unique hl hr
  simpa only [← mul_assoc, mul_inv_cancel₀ (euler_ne_zero (q^3) hq3), one_mul] using hh

end
end Borwein.EulerPentagonalLimit
