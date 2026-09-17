import Borwein.PhaseIntegral
import Mathlib.Analysis.Real.Pi.Bounds

/-! Zero avoidance and quadratic phase bounds at τ=0 on the open first-root arc. -/

namespace Borwein.PhaseBoundary
noncomputable section
open scoped BigOperators
open Borwein.PhaseGap Borwein.PhaseIntegral

theorem geometric_five_unit_ne_zero (v : ℝ) (hv : |v| < 2*Real.pi/5) :
    (∑ j : Fin 5, Complex.exp ((v : ℂ)*Complex.I) ^ (j : ℕ)) ≠ 0 := by
  by_cases hvzero : v = 0
  · subst v; norm_num
  intro hzero
  have hsum : (∑ j ∈ Finset.range 5, Complex.exp ((v : ℂ)*Complex.I)^j) = 0 := by
    simpa only [Fin.sum_univ_eq_sum_range] using hzero
  have hgeom := geom_sum_mul (Complex.exp ((v : ℂ)*Complex.I)) 5
  rw [hsum, zero_mul] at hgeom
  have hpow : Complex.exp ((v : ℂ)*Complex.I)^5 = 1 := sub_eq_zero.mp hgeom.symm
  rw [← Complex.exp_nat_mul] at hpow
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hpow
  have him := congrArg Complex.im hk
  norm_num at him
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hv
  have hklo : (-1 : ℝ) < (k : ℝ) := by
    apply (mul_lt_mul_iff_of_pos_right (show 0 < 2*Real.pi by positivity)).mp
    nlinarith
  have hkhi : (k : ℝ) < (1 : ℝ) := by
    apply (mul_lt_mul_iff_of_pos_right (show 0 < 2*Real.pi by positivity)).mp
    nlinarith
  have hk0 : k = 0 := by
    have ha : (-1 : ℤ) < k := by exact_mod_cast hklo
    have hb : k < (1 : ℤ) := by exact_mod_cast hkhi
    omega
  simp [hk0] at him
  exact hvzero (by linarith)

theorem radial_amplitude_zero_tau_ne_zero (v : ℝ) (hv : |v| < 2*Real.pi/5) :
    amplitude (radialWeight 0) (fun j => (j : ℝ)*v) ≠ 0 := by
  rw [radial_amplitude_eq_geometric]
  apply div_ne_zero
  · simpa using geometric_five_unit_ne_zero v hv
  · norm_num

theorem phase_zero_tau_ne_zero (t x : ℝ) (ht : |t| < 2*Real.pi/5)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : phase 0 t x ≠ 0 := by
  have hv : |t*x| < 2*Real.pi/5 := by
    calc
      |t*x| = |t| * x := by rw [abs_mul, abs_of_nonneg hx.1]
      _ ≤ |t| := mul_le_of_le_one_right (abs_nonneg _) hx.2
      _ < 2*Real.pi/5 := ht
  simpa [phase] using radial_amplitude_zero_tau_ne_zero (t*x) hv

theorem integral_phase_gap_zero_tau (t : ℝ) (ht : |t| < 2*Real.pi/5) :
    (∫ x in (0 : ℝ)..1, gapDensity 0 t x + gapDensity 0 t x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, -Real.log ‖phase 0 t x‖ := by
  apply integral_norm_log_quadratic (phase 0 t) (gapDensity 0 t) 0 1 (by norm_num)
    (continuous_phase 0 t).continuousOn (continuous_gapDensity 0 t).continuousOn
  · intro x _
    rw [gapDensity, ← pairGap_eq_groupedGap]
    exact pairGap_nonneg _ _ (fun j => (radialWeight_pos (0*x) j).le)
  · intro x hx
    exact phase_zero_tau_ne_zero t x ht hx
  · intro x _
    simpa only [phase, gapDensity, pairGap_eq_groupedGap] using
      amplitude_norm_sq (radialWeight (0*x)) (fun j => (j : ℝ)*(t*x))
        (radialWeight_sum (0*x))

theorem phase_ne_zero_nonneg (τ t x : ℝ) (hτ : 0 ≤ τ) (ht : |t| < 2*Real.pi/5)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : phase τ t x ≠ 0 := by
  rcases eq_or_lt_of_le hτ with hzero | hpos
  · subst τ; exact phase_zero_tau_ne_zero t x ht hx
  · exact phase_ne_zero τ t x hpos hx.1

theorem integral_phase_gap_nonneg (τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| < 2*Real.pi/5) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖ := by
  rcases eq_or_lt_of_le hτ with hzero | hpos
  · subst τ; exact integral_phase_gap_zero_tau t ht
  · exact integral_phase_gap τ t hpos

/-- Includes the actual middle-arc endpoint 1.2 used by the numerical certificates. -/
theorem integral_phase_gap_middle (τ t : ℝ) (hτ : 0 ≤ τ) (ht : |t| ≤ 6/5) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖ := by
  apply integral_phase_gap_nonneg τ t hτ
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  linarith

theorem R_re_difference_ge_quadratic_nonneg (τ t : ℝ) (hτ : 0 ≤ τ)
    (ht : |t| < 2*Real.pi/5) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      radialR τ - (complexR ((τ : ℂ) - (t : ℂ)*Complex.I)).re := by
  rw [← integral_phase_eq_R_re_difference_of_ne_zero τ t
    (fun x hx => phase_ne_zero_nonneg τ t x hτ ht hx)]
  exact integral_phase_gap_nonneg τ t hτ ht

end
end Borwein.PhaseBoundary
