import Borwein.WatsonSpecializedTerms
import Borwein.WatsonPochhammerLimit

set_option autoImplicit false

namespace Borwein.WatsonSumLimit
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerGaussianLimit WatsonThetaExponent
  WatsonFiniteTerms WatsonPochhammer WatsonPochhammerLimit WatsonSpecializedTerms Filter
open scoped Topology

def normalizer (x : ℂ) (r : ℕ) : ℂ :=
  euler (x^5)*(limit (x^5) (x^(2*r)))⁻¹*(limit (x^5) (x^(10-2*r)))⁻¹

theorem row_tendsto (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) (k : ℤ) :
    Tendsto (fun n : ℕ => row (x^5) ((x^r)⁻¹) n k) atTop
      (𝓝 (normalizer x r*term x r k)) := by
  have hx5 : ‖x^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  have hA := inverse_shifted_tendsto (x^5) (x^(2*r)) hx5
    (WatsonSpecialization.positive_factors x hx (2*r) (by omega)) (-k)
  have hB := inverse_shifted_tendsto (x^5) (x^(10-2*r)) hx5
    (WatsonSpecialization.positive_factors x hx (10-2*r) (by omega)) k
  have hE := (finiteEuler_tendsto (x^5) hx5).comp
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 2*n by omega) tendsto_id)
  have hh := ((hE.mul_const (term x r k)).mul hA).mul hB
  have he : euler (x^5)*term x r k*(limit (x^5) (x^(2*r)))⁻¹*
      (limit (x^5) (x^(10-2*r)))⁻¹=normalizer x r*term x r k := by
    unfold normalizer
    ring
  rw [he] at hh
  simpa only [Function.comp_def, row_eq x hx0 r hr0 hr, sub_eq_add_neg] using hh

theorem row_uniform_bound (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, ∀ k : ℤ,
      ‖row (x^5) ((x^r)⁻¹) n k‖ ≤
        M*(‖x‖^(degree r 0 k)+‖x‖^(degree r 1 k)) := by
  have hx5 : ‖x^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg x) hx (by norm_num)
  obtain ⟨A,hA,hbA⟩ := (Metric.isBounded_range_of_tendsto _
    (finiteEuler_tendsto (x^5) hx5)).exists_pos_norm_le
  obtain ⟨B,hB,hbB⟩ := inverse_bounded (x^5) (x^(2*r)) hx5
    (WatsonSpecialization.positive_factors x hx (2*r) (by omega))
  obtain ⟨C,hC,hbC⟩ := inverse_bounded (x^5) (x^(10-2*r)) hx5
    (WatsonSpecialization.positive_factors x hx (10-2*r) (by omega))
  refine ⟨A*B*C,by positivity,fun n k => ?_⟩
  rw [row_eq x hx0 r hr0 hr, norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ A*(‖x‖^(degree r 0 k)+‖x‖^(degree r 1 k))*B*C := by
      gcongr
      · exact hbA _ ⟨2*n,rfl⟩
      · exact term_bound x r k
      · exact hbB _
      · exact hbC _
    _ = _ := by ring

theorem sum_tendsto (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2) :
    Tendsto (fun n : ℕ => ∑' k : ℤ, row (x^5) ((x^r)⁻¹) n k) atTop
      (𝓝 (normalizer x r*(∑' k : ℤ, term x r k))) := by
  obtain ⟨M,hM,hb⟩ := row_uniform_bound x hx hx0 r hr0 hr
  have hh := tendsto_tsum_of_dominated_convergence
    (((majorant_summable x hx r 0 hr0 hr (by omega)).add
      (majorant_summable x hx r 1 hr0 hr (by omega))).mul_left M)
    (fun k => row_tendsto x hx hx0 r hr0 hr k)
    (Eventually.of_forall hb)
  simpa only [tsum_mul_left] using hh

end
end Borwein.WatsonSumLimit
