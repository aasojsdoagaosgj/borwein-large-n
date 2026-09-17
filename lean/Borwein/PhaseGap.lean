import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! The quadratic logarithmic phase-gap bound. No numerical certificate is assumed. -/

namespace Borwein.PhaseGap

noncomputable section

open scoped BigOperators

theorem log_quadratic {s : ℝ} (hs : 0 ≤ s) (hlt : 2 * s < 1) :
    s + s ^ 2 ≤ -Real.log (1 - 2 * s) / 2 := by
  have habs : |2 * s| < 1 := by rw [abs_of_nonneg (by positivity)]; exact hlt
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have h := sum_le_hasSum (Finset.range 2)
    (fun (i : ℕ) _ => show 0 ≤ (2 * s) ^ (i + 1) / ((i : ℝ) + 1) by positivity) hsum
  norm_num [Finset.sum_range_succ] at h
  nlinarith

theorem norm_log_quadratic (z : ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hz : z ≠ 0) (hid : ‖z‖ ^ 2 = 1 - 2 * s) :
    s + s ^ 2 ≤ -Real.log ‖z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlt : 2 * s < 1 := by nlinarith [sq_pos_of_pos hn]
  have h := log_quadratic hs hlt
  rw [← hid, Real.log_pow] at h
  norm_num at h ⊢
  linarith

def amplitude (p θ : Fin 5 → ℝ) : ℂ :=
  ⟨∑ j, p j * Real.cos (θ j), ∑ j, p j * Real.sin (θ j)⟩

theorem amplitude_eq_exp_sum (p θ : Fin 5 → ℝ) :
    amplitude p θ = ∑ j, (p j : ℂ) * Complex.exp ((θ j : ℂ) * Complex.I) := by
  apply Complex.ext <;> simp [amplitude, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

def pairTerm (p θ : Fin 5 → ℝ) (i j : Fin 5) : ℝ :=
  p i * p j * (1 - Real.cos (θ j - θ i))

def pairGap (p θ : Fin 5 → ℝ) : ℝ :=
  pairTerm p θ 0 1 + pairTerm p θ 0 2 + pairTerm p θ 0 3 + pairTerm p θ 0 4 +
  pairTerm p θ 1 2 + pairTerm p θ 1 3 + pairTerm p θ 1 4 +
  pairTerm p θ 2 3 + pairTerm p θ 2 4 + pairTerm p θ 3 4

theorem pairTerm_nonneg (p θ : Fin 5 → ℝ) (hp : ∀ j, 0 ≤ p j) (i j) :
    0 ≤ pairTerm p θ i j :=
  mul_nonneg (mul_nonneg (hp i) (hp j)) (sub_nonneg.mpr (Real.cos_le_one _))

theorem pairGap_nonneg (p θ : Fin 5 → ℝ) (hp : ∀ j, 0 ≤ p j) :
    0 ≤ pairGap p θ := by
  unfold pairGap
  repeat' apply add_nonneg
  all_goals exact pairTerm_nonneg p θ hp _ _

theorem amplitude_norm_sq (p θ : Fin 5 → ℝ) (hmass : ∑ j, p j = 1) :
    ‖amplitude p θ‖ ^ 2 = 1 - 2 * pairGap p θ := by
  have hm2 := congrArg (fun x : ℝ => x ^ 2) hmass
  simp only [Fin.sum_univ_five, one_pow] at hm2
  simp [amplitude, Complex.sq_norm, Complex.normSq_apply, Fin.sum_univ_five,
    pairGap, pairTerm, Real.cos_sub]
  linear_combination hm2 +
    (p 0)^2 * Real.sin_sq_add_cos_sq (θ 0) +
    (p 1)^2 * Real.sin_sq_add_cos_sq (θ 1) +
    (p 2)^2 * Real.sin_sq_add_cos_sq (θ 2) +
    (p 3)^2 * Real.sin_sq_add_cos_sq (θ 3) +
    (p 4)^2 * Real.sin_sq_add_cos_sq (θ 4)

theorem amplitude_log_gap (p θ : Fin 5 → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hmass : ∑ j, p j = 1) (hz : amplitude p θ ≠ 0) :
    pairGap p θ + pairGap p θ ^ 2 ≤ -Real.log ‖amplitude p θ‖ :=
  norm_log_quadratic _ _ (pairGap_nonneg p θ hp) hz (amplitude_norm_sq p θ hmass)

def groupedGap (p : Fin 5 → ℝ) (v : ℝ) : ℝ :=
  (p 0*p 1 + p 1*p 2 + p 2*p 3 + p 3*p 4) * (1 - Real.cos v) +
  (p 0*p 2 + p 1*p 3 + p 2*p 4) * (1 - Real.cos (2*v)) +
  (p 0*p 3 + p 1*p 4) * (1 - Real.cos (3*v)) +
  p 0*p 4 * (1 - Real.cos (4*v))

theorem pairGap_eq_groupedGap (p : Fin 5 → ℝ) (v : ℝ) :
    pairGap p (fun j => (j : ℝ) * v) = groupedGap p v := by
  norm_num [pairGap, pairTerm, groupedGap]
  ring_nf

def radialWeight (y : ℝ) (j : Fin 5) : ℝ :=
  Real.exp (-(j : ℝ) * y) / ∑ k : Fin 5, Real.exp (-(k : ℝ) * y)

theorem radialDenominator_pos (y : ℝ) :
    0 < ∑ k : Fin 5, Real.exp (-(k : ℝ) * y) := by
  apply Finset.sum_pos
  · intro i _; exact Real.exp_pos _
  · exact Finset.univ_nonempty

theorem radialWeight_pos (y : ℝ) (j : Fin 5) : 0 < radialWeight y j :=
  div_pos (Real.exp_pos _) (radialDenominator_pos y)

theorem radialWeight_sum (y : ℝ) : ∑ j, radialWeight y j = 1 := by
  simp only [radialWeight, ← Finset.sum_div]
  exact div_self (ne_of_gt (radialDenominator_pos y))

theorem radial_amplitude_eq_geometric (y v : ℝ) :
    amplitude (radialWeight y) (fun j => (j : ℝ)*v) =
      (∑ j : Fin 5, Complex.exp ((-y : ℝ) + (v : ℂ)*Complex.I) ^ (j : ℕ)) /
        ((∑ k : Fin 5, Real.exp (-(k : ℝ)*y) : ℝ) : ℂ) := by
  rw [amplitude_eq_exp_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [radialWeight, Complex.ofReal_div, div_mul_eq_mul_div]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem geometric_five_ne_zero (q : ℂ) (hq : ‖q‖ < 1) :
    (∑ j : Fin 5, q ^ (j : ℕ)) ≠ 0 := by
  intro hzero
  have hgeom := geom_sum_mul q 5
  have hsum : (∑ j ∈ Finset.range 5, q ^ j) = 0 := by
    simpa only [Fin.sum_univ_eq_sum_range] using hzero
  rw [hsum, zero_mul] at hgeom
  have hpow : q ^ 5 = 1 := sub_eq_zero.mp hgeom.symm
  have hnorm : ‖q‖ ^ 5 = 1 := by simpa using congrArg norm hpow
  have hlt : ‖q‖ ^ 5 < 1 := pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  linarith

theorem radial_amplitude_ne_zero (y v : ℝ) (hy : 0 < y) :
    amplitude (radialWeight y) (fun j => (j : ℝ)*v) ≠ 0 := by
  rw [radial_amplitude_eq_geometric]
  apply div_ne_zero
  · apply geometric_five_ne_zero
    rw [Complex.norm_exp]
    simpa using (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hy))
  · exact_mod_cast ne_of_gt (radialDenominator_pos y)

theorem radial_log_gap (y v : ℝ)
    (hz : amplitude (radialWeight y) (fun j => (j : ℝ)*v) ≠ 0) :
    groupedGap (radialWeight y) v + groupedGap (radialWeight y) v ^ 2 ≤
      -Real.log ‖amplitude (radialWeight y) (fun j => (j : ℝ)*v)‖ := by
  simpa only [pairGap_eq_groupedGap] using
    amplitude_log_gap (radialWeight y) (fun j => (j : ℝ)*v)
      (fun j => (radialWeight_pos y j).le) (radialWeight_sum y) hz

theorem integral_norm_log_quadratic (z : ℝ → ℂ) (s : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hcZ : ContinuousOn z (Set.Icc a b))
    (hcS : ContinuousOn s (Set.Icc a b))
    (hs : ∀ x ∈ Set.Icc a b, 0 ≤ s x)
    (hz : ∀ x ∈ Set.Icc a b, z x ≠ 0)
    (hid : ∀ x ∈ Set.Icc a b, ‖z x‖ ^ 2 = 1 - 2*s x) :
    (∫ x in a..b, s x + s x ^ 2) ≤ ∫ x in a..b, -Real.log ‖z x‖ := by
  have hcL : ContinuousOn (fun x => -Real.log ‖z x‖) (Set.Icc a b) :=
    (hcZ.norm.log (fun x hx => norm_ne_zero_iff.mpr (hz x hx))).neg
  apply intervalIntegral.integral_mono_on hab
    ((hcS.add (hcS.pow 2)).intervalIntegrable_of_Icc hab)
    (hcL.intervalIntegrable_of_Icc hab)
  intro x hx
  exact norm_log_quadratic (z x) (s x) (hs x hx) (hz x hx) (hid x hx)

@[fun_prop]
theorem continuous_radialWeight (j : Fin 5) : Continuous (fun y => radialWeight y j) := by
  unfold radialWeight
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro y; exact ne_of_gt (radialDenominator_pos y)

def phase (τ t x : ℝ) : ℂ :=
  amplitude (radialWeight (τ*x)) (fun j => (j : ℝ)* (t*x))

def gapDensity (τ t x : ℝ) : ℝ := groupedGap (radialWeight (τ*x)) (t*x)

theorem continuous_phase (τ t : ℝ) : Continuous (phase τ t) := by
  have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (τ*x) j) := by fun_prop
  unfold phase
  simp_rw [amplitude_eq_exp_sum]
  fun_prop

theorem continuous_gapDensity (τ t : ℝ) : Continuous (gapDensity τ t) := by
  have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (τ*x) j) := by fun_prop
  unfold gapDensity groupedGap
  fun_prop

theorem phase_ne_zero (τ t x : ℝ) (hτ : 0 < τ) (hx : 0 ≤ x) : phase τ t x ≠ 0 := by
  rcases eq_or_lt_of_le hx with hzero | hpos
  · subst x
    have hmass := radialWeight_sum 0
    have hphase : phase τ t 0 = 1 := by
      apply Complex.ext <;> simp [phase, amplitude, hmass]
    rw [hphase]; exact one_ne_zero
  · exact radial_amplitude_ne_zero (τ*x) (t*x) (mul_pos hτ hpos)

/-- The S+S² integrated phase-gap bound, with zero avoidance proved for τ>0. -/
theorem integral_phase_gap (τ t : ℝ) (hτ : 0 < τ) :
    (∫ x in (0 : ℝ)..1, gapDensity τ t x + gapDensity τ t x ^ 2) ≤
      ∫ x in (0 : ℝ)..1, -Real.log ‖phase τ t x‖ := by
  apply integral_norm_log_quadratic (phase τ t) (gapDensity τ t) 0 1 (by norm_num)
    (continuous_phase τ t).continuousOn (continuous_gapDensity τ t).continuousOn
  · intro x _
    rw [gapDensity, ← pairGap_eq_groupedGap]
    exact pairGap_nonneg _ _ (fun j => (radialWeight_pos (τ*x) j).le)
  · intro x hx
    exact phase_ne_zero τ t x hτ hx.1
  · intro x _
    simpa only [phase, gapDensity, pairGap_eq_groupedGap] using
      amplitude_norm_sq (radialWeight (τ*x)) (fun j => (j : ℝ)*(t*x))
        (radialWeight_sum (τ*x))

end
end Borwein.PhaseGap
