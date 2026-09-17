import Borwein.EulerPentagonalFinite
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

namespace Borwein.EulerGaussianLimit
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerQBinomial Filter
open scoped Topology

theorem euler_ne_zero (q : ℂ) (hq : ‖q‖ < 1) : euler q ≠ 0 := by
  simpa only [tailEuler, Nat.add_zero, euler] using tailEuler_ne_zero 0 q hq

theorem finiteEuler_tendsto (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => finiteEuler n q) atTop (𝓝 (euler q)) := by
  simpa only [finiteEuler, Nat.add_zero, euler] using
    (tail_multipliable 0 q hq).tendsto_prod_tprod_nat

theorem inverse_tendsto (q : ℂ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => (finiteEuler n q)⁻¹) atTop (𝓝 ((euler q)⁻¹)) :=
  (finiteEuler_tendsto q hq).inv₀ (euler_ne_zero q hq)

/-- All finite Gaussian coefficients share one bound for each point of the unit disk. -/
theorem gaussian_bounded (q : ℂ) (hq : ‖q‖ < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ n k : ℕ, ‖gaussian q n k‖ ≤ M := by
  obtain ⟨A, hA, hbA⟩ := (Metric.isBounded_range_of_tendsto _ (finiteEuler_tendsto q hq)).exists_pos_norm_le
  obtain ⟨B, hB, hbB⟩ := (Metric.isBounded_range_of_tendsto _ (inverse_tendsto q hq)).exists_pos_norm_le
  refine ⟨A*B*B, by positivity, ?_⟩
  intro n k
  by_cases hk : k ≤ n
  · simp only [gaussian, if_pos hk, div_eq_mul_inv, mul_inv_rev, norm_mul]
    exact mul_le_mul (hbA _ ⟨n,rfl⟩)
      (mul_le_mul (hbB _ ⟨n-k,rfl⟩) (hbB _ ⟨k,rfl⟩) (norm_nonneg _) hB.le)
      (by positivity) hA.le |>.trans_eq (by ring)
  · simp only [gaussian, if_neg hk, norm_zero]
    positivity

/-- Both lower indices tending to infinity give the central Gaussian limit. -/
theorem gaussian_tendsto (q : ℂ) (f g : ℕ → ℕ) (hq : ‖q‖ < 1)
    (hf : Tendsto f atTop atTop) (hg : Tendsto g atTop atTop)
    (hd : Tendsto (fun n => f n-g n) atTop atTop)
    (hle : ∀ᶠ n in atTop, g n ≤ f n) :
    Tendsto (fun n => gaussian q (f n) (g n)) atTop (𝓝 ((euler q)⁻¹)) := by
  have hp := finiteEuler_tendsto q hq
  have hh := (hp.comp hf).div ((hp.comp hg).mul (hp.comp hd))
    (mul_ne_zero (euler_ne_zero q hq) (euler_ne_zero q hq))
  have he : euler q/(euler q*euler q)=(euler q)⁻¹ := by field_simp
  rw [he] at hh
  apply hh.congr'
  filter_upwards [hle] with n hn
  simp only [Function.comp_def, Pi.div_apply, gaussian, if_pos hn]

theorem central_positive (q : ℂ) (k : ℕ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => gaussian q (2*n) (n+k)) atTop (𝓝 ((euler q)⁻¹)) := by
  apply gaussian_tendsto q _ _ hq
  · exact tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n : ℕ, n ≤ 2*n) tendsto_id
  · exact tendsto_add_atTop_nat k
  · convert tendsto_sub_atTop_nat k using 1
    ext n
    omega
  · filter_upwards [eventually_ge_atTop k] with n hn
    omega

theorem central_negative (q : ℂ) (k : ℕ) (hq : ‖q‖ < 1) :
    Tendsto (fun n : ℕ => gaussian q (2*n) (n-k)) atTop (𝓝 ((euler q)⁻¹)) := by
  apply gaussian_tendsto q _ _ hq
  · exact tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n : ℕ, n ≤ 2*n) tendsto_id
  · exact tendsto_sub_atTop_nat k
  · exact tendsto_atTop_mono (fun n : ℕ => by omega : ∀ n : ℕ, n ≤ 2*n-(n-k)) tendsto_id
  · exact Eventually.of_forall (fun n => by omega)

end
end Borwein.EulerGaussianLimit
