import Borwein.EndpointActualPhase

set_option autoImplicit false

namespace Borwein.EndpointPhaseBounds
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseSeries EndpointPhaseDerivatives

def sharpMajorant (n h j : ℕ) (v : ℝ) (k : ℕ) : ℝ :=
  (4/(5*(k:ℝ)^2))*frequency n k^h*(Real.exp (-frequency n k*v)/v^(j+1))

theorem coefficient_sharp_bound (k : ℕ) : |coefficient k| ≤ 4/(5*(k:ℝ)^2) := by
  rw [coefficient, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ 5*(k:ℝ)^2)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  split_ifs <;> norm_num

theorem component_sharp_bound (n h j : ℕ) (v y : ℝ) (k : ℕ) (hv : 0 < v) :
    ‖component n h j v y k‖ ≤ sharpMajorant n h j v k := by
  rw [component, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (frequency_nonneg n k)]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right (coefficient_sharp_bound k) (pow_nonneg (frequency_nonneg n k) h))
    (atom_bound (frequency n k) j v y hv) (norm_nonneg _)
    (mul_nonneg (by positivity) (pow_nonneg (frequency_nonneg n k) h))

theorem sharpMajorant_nonneg (n h j : ℕ) (v : ℝ) (k : ℕ) (hv : 0 < v) :
    0 ≤ sharpMajorant n h j v k := by
  unfold sharpMajorant
  exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg (frequency_nonneg n k) h)) (by positivity)

theorem sharpMajorant_le (n h j : ℕ) (v : ℝ) (k : ℕ) (hv : 0 < v) :
    sharpMajorant n h j v k ≤ majorant n h j v k := by
  have hc : (4:ℝ)/(5*(k:ℝ)^2) ≤ 1 := by
    by_cases hk : k=0
    · simp [hk]
    · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
      apply (div_le_one (by positivity : (0:ℝ) < 5*(k:ℝ)^2)).mpr
      nlinarith
  have hh := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (pow_nonneg (frequency_nonneg n k) h) (by positivity : 0 ≤ Real.exp (-frequency n k*v)/v^(j+1)))
  simpa only [one_mul, sharpMajorant, majorant, mul_assoc, mul_div_assoc] using hh

theorem sharpMajorant_summable (n h j : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Summable (sharpMajorant n h j v) :=
  Summable.of_nonneg_of_le (fun k => sharpMajorant_nonneg n h j v k hv)
    (fun k => sharpMajorant_le n h j v k hv) (majorant_summable n h j v hn hv)

theorem series_sharp_bound (n h j : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    ‖series n h j v y‖ ≤ ∑' k : ℕ, sharpMajorant n h j v k := by
  exact (norm_tsum_le_tsum_norm (component_summable n h j v y hn hv).norm).trans
    ((component_summable n h j v y hn hv).norm.tsum_le_tsum
      (fun k => component_sharp_bound n h j v y k hv) (sharpMajorant_summable n h j v hn hv))

theorem q2_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    ‖q2 n v y‖ ≤ (∑' k, sharpMajorant n 2 0 v k)+2*(∑' k, sharpMajorant n 1 1 v k)+
      2*(∑' k, sharpMajorant n 0 2 v k) := by
  have h1 := series_sharp_bound n 2 0 v y hn hv
  have h2 := series_sharp_bound n 1 1 v y hn hv
  have h3 := series_sharp_bound n 0 2 v y hn hv
  have hb := (norm_add_le (series n 2 0 v y+2*series n 1 1 v y) (2*series n 0 2 v y)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  norm_num [norm_mul] at hb
  exact hb.trans (by nlinarith)

theorem q3_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    ‖q3 n v y‖ ≤ (∑' k, sharpMajorant n 3 0 v k)+3*(∑' k, sharpMajorant n 2 1 v k)+
      6*(∑' k, sharpMajorant n 1 2 v k)+6*(∑' k, sharpMajorant n 0 3 v k) := by
  have h0 := series_sharp_bound n 3 0 v y hn hv
  have h1 := series_sharp_bound n 2 1 v y hn hv
  have h2 := series_sharp_bound n 1 2 v y hn hv
  have h3 := series_sharp_bound n 0 3 v y hn hv
  rw [q3, norm_neg]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  apply (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans
  norm_num [norm_mul]
  nlinarith

end
end Borwein.EndpointPhaseBounds
