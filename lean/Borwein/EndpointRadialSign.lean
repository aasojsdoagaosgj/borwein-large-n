import Borwein.EndpointScalarCorrection

set_option autoImplicit false

namespace Borwein.EndpointRadialSign
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseSeries EndpointPhaseDerivatives EndpointActualPhase
  EndpointTailGlobalLog EndpointScalarCorrection EndpointRadialNormalization

theorem radialX_lt_one (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) : radialX n v < 1 := by
  unfold radialX
  apply Real.exp_lt_one_iff.mpr
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  push_cast
  nlinarith

theorem component_real (n h j k : ℕ) (v : ℝ) :
    (component n h j v 0 k).re=coefficient k*frequency n k^h*Real.exp (-frequency n k*v)/v^(j+1) := by
  have he : component n h j v 0 k=
      ((coefficient k*frequency n k^h*Real.exp (-frequency n k*v)/v^(j+1):ℝ):ℂ) := by
    have hE : exp (-(frequency n k:ℂ)*(v:ℂ))=((Real.exp (-frequency n k*v):ℝ):ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp only [component, EndpointPhaseAtoms.atom, coordinate, Complex.ofReal_zero, zero_mul, add_zero]
    rw [hE]
    push_cast
    ring
  rw [he, Complex.ofReal_re]

theorem component_first (n k : ℕ) (v : ℝ) (hv : 0 < v) :
    (component n 1 0 v 0 k).re=(n:ℝ)/v*correction (radialX n v) 1 k := by
  rw [component_real, geometric_identity]
  change coefficient k*frequency n k^1*(radialX n v)^k/v^(0+1)=_
  by_cases hk : k=0
  · subst k
    simp [coefficient, frequency, correction, sparse, term]
  · have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    unfold coefficient frequency correction sparse term
    split_ifs <;> push_cast <;> field_simp <;> ring

theorem component_second (n k : ℕ) (v : ℝ) (hv : 0 < v) :
    (component n 0 1 v 0 k).re=correction (radialX n v) 2 k/(5*v^2) := by
  rw [component_real, geometric_identity]
  change coefficient k*frequency n k^0*(radialX n v)^k/v^(1+1)=_
  by_cases hk : k=0
  · subst k
    simp [coefficient, frequency, correction, sparse, term]
  · have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
    unfold coefficient correction sparse term
    split_ifs <;> field_simp <;> ring

theorem series_first_nonpos (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    (series n 1 0 v 0).re ≤ 0 := by
  have hr := radialX_positive n v
  have hR := radialX_lt_one n v hn hv
  have hs := ((correction_hasSum (radialX n v) 1 (by norm_num) hr.le hR).mul_left ((n:ℝ)/v)).congr_fun
    (fun k => component_first n k v hv)
  have hc := Complex.reCLM.hasSum (component_summable n 1 0 v 0 hn hv).hasSum
  change HasSum (fun k : ℕ => (component n 1 0 v 0 k).re) (series n 1 0 v 0).re at hc
  rw [hc.unique hs]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
    (correction_sum_nonpos (radialX n v) 1 (Or.inl rfl) hr.le hR)

theorem series_second_nonpos (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    (series n 0 1 v 0).re ≤ 0 := by
  have hr := radialX_positive n v
  have hR := radialX_lt_one n v hn hv
  have hs := ((correction_hasSum (radialX n v) 2 (by norm_num) hr.le hR).div_const (5*v^2)).congr_fun
    (fun k => component_second n k v hv)
  have hc := Complex.reCLM.hasSum (component_summable n 0 1 v 0 hn hv).hasSum
  change HasSum (fun k : ℕ => (component n 0 1 v 0 k).re) (series n 0 1 v 0).re at hc
  rw [hc.unique hs]
  exact div_nonpos_of_nonpos_of_nonneg
    (correction_sum_nonpos (radialX n v) 2 (Or.inr rfl) hr.le hR) (by positivity)

theorem correction_derivative_nonneg (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    0 ≤ (q1 n v 0).re := by
  simp only [q1, Complex.neg_re, Complex.add_re]
  linarith [series_first_nonpos n v hn hv, series_second_nonpos n v hn hv]

theorem first_main_upper (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    -(f1 n v 0).re ≤ A/v^2 := by
  have he : (f1 n v 0).re=-A/v^2+(q1 n v 0).re := by
    simp only [f1, EndpointPhaseAtoms.atom, coordinate, Complex.ofReal_zero, zero_mul, add_zero,
      neg_zero, Complex.exp_zero, show (1:ℕ)+1=2 by rfl]
    have hm : -(A:ℂ)*(1/(v:ℂ)^2)=((-A/v^2:ℝ):ℂ) := by push_cast; ring
    rw [hm, Complex.add_re, Complex.ofReal_re]
  rw [neg_div] at he
  rw [he]
  linarith [correction_derivative_nonneg n v hn hv]

end
end Borwein.EndpointRadialSign
