import Borwein.EndpointCoefficientConnection
import Borwein.EndpointOuterGeometry

set_option autoImplicit false

namespace Borwein.EndpointSignedRadialLoss
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseSeries EndpointPhaseDerivatives EndpointActualPhase
  EndpointTailGlobalLog EndpointRadialNormalization

theorem coefficient_lower (k : ℕ) : -(1/5:ℝ) ≤ coefficient k := by
  by_cases hk : k=0
  · simp [hk, coefficient]
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hD : (5:ℝ) ≤ 5*(k:ℝ)^2 := by nlinarith
  have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 5) hD
  unfold coefficient
  split_ifs
  · have hp : 0 ≤ (4:ℝ)/(5*(k:ℝ)^2) := by positivity
    linarith
  · rw [neg_div]
    linarith

theorem component_real (n k : ℕ) (v : ℝ) :
    (component n 0 0 v 0 k).re=coefficient k*Real.exp (-frequency n k*v)/v := by
  have he : component n 0 0 v 0 k=((coefficient k*Real.exp (-frequency n k*v)/v:ℝ):ℂ) := by
    have hE : exp (-(frequency n k:ℂ)*(v:ℂ))=((Real.exp (-frequency n k*v):ℝ):ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    simp only [component, atom, coordinate, Complex.ofReal_zero, zero_mul, add_zero,
      pow_zero, mul_one, Nat.zero_add, pow_one]
    rw [hE]
    push_cast
    ring
  rw [he, Complex.ofReal_re]

theorem component_lower (n k : ℕ) (v : ℝ) (hv : 0 < v) :
    -(radialX n v)^k/(5*v) ≤ (component n 0 0 v 0 k).re := by
  rw [component_real, geometric_identity]
  have hr := radialX_positive n v
  have hh := mul_le_mul_of_nonneg_right (coefficient_lower k)
    (by positivity : 0 ≤ (radialX n v)^k/v)
  convert! hh using 1 <;> dsimp [radialX] <;> ring

theorem correction_lower (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    -radialX n v/(5*v*(1-radialX n v)) ≤ (q0 n v 0).re := by
  have hr := radialX_positive n v
  have hR : radialX n v < 1 := (radialX_small n v hτ).trans_lt (by norm_num)
  have hg : HasSum (fun k : ℕ => -(radialX n v)^(k+1)/(5*v))
      (-radialX n v/(5*v*(1-radialX n v))) := by
    convert! (((hasSum_geometric_of_lt_one hr.le hR).mul_left (radialX n v)).neg).div_const (5*v) using 1
    · ext k
      rw [pow_succ]
      ring
    · field_simp
  have hs : HasSum (fun k : ℕ => component n 0 0 v 0 (k+1)) (q0 n v 0) := by
    have hh := (hasSum_nat_add_iff' 1).mpr (component_summable n 0 0 v 0 hn hv).hasSum
    simpa [q0, series, component, coefficient, Finset.sum_range_succ] using hh
  have hsr := Complex.reCLM.hasSum hs
  change HasSum (fun k : ℕ => (component n 0 0 v 0 (k+1)).re) (q0 n v 0).re at hsr
  rw [← hg.tsum_eq, ← hsr.tsum_eq]
  exact hg.summable.tsum_le_tsum (fun k => component_lower n (k+1) v hv) hsr.summable

theorem radial_loss (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    A/v-(n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v) ≤ radialX n v/(5*v*(1-radialX n v)) := by
  have he := congrArg Complex.re (EndpointSaddleIdentification.radial_f0_value n v hn hv)
  have hf : (f0 n v 0).re=A/v+(q0 n v 0).re := by
    simp [f0, atom, coordinate, Complex.mul_re, Complex.normSq_apply]
    ring
  rw [hf, Complex.ofReal_re] at he
  have hl := correction_lower n v hn hv hτ
  rw [neg_div] at hl
  linarith

theorem gap_budget (n : ℕ) (v : ℝ) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    (1/30:ℝ) ≤ 1/25-radialX n v-radialX n v/(5*(1-radialX n v)) := by
  have hr := radialX_positive n v
  have hX := radialX_small n v hτ
  have hD : 0 < 5*(1-radialX n v) := by linarith
  have hq : radialX n v/(5*(1-radialX n v)) ≤ (1/995:ℝ) := by
    apply (div_le_iff₀ hD).mpr
    linarith
  linarith

theorem tail_norm (n : ℕ) (q : ℂ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hq : ‖q‖=Real.exp (-v)) :
    ‖EndpointFiniteConnection.tail n q‖ ≤ Real.exp (radialX n v/v) := by
  have hq1 : ‖q‖ < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  rw [← EndpointTailLog.exp_tailLog n q hq1, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  exact (Complex.re_le_norm _).trans (endpoint_log_bound n q v hn hv hV hτ hq)

end
end Borwein.EndpointSignedRadialLoss
