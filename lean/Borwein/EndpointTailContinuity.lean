import Borwein.EndpointTailLog
import Borwein.EndpointEtaTailBound
import Borwein.EndpointPhaseAtoms
import Mathlib.Analysis.Normed.Group.FunctionSeries

set_option autoImplicit false

namespace Borwein.EndpointTailContinuity
noncomputable section
open Complex EndpointTailLog EndpointPhaseAtoms

theorem factor_continuous (q : ℝ → ℂ) (hq : Continuous q)
    (hB : ∀ y, ‖q y‖ < 1) (k : ℕ) (hk : 0 < k) :
    Continuous (fun y => log (1-(q y)^k)) := by
  apply Continuous.clog (continuous_const.sub (hq.pow k))
  intro y
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hb : ‖(q y)^k‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (hB y) (by omega)
  have hr := Complex.re_le_norm ((q y)^k)
  change 0 < (1-(q y)^k).re
  simp only [Complex.sub_re, Complex.one_re]
  linarith

theorem inverseLog_continuous (N : ℕ) (q : ℝ → ℂ) (r : ℝ)
    (hq : Continuous q) (hr : 0 ≤ r) (hR : r < 1) (hB : ∀ y, ‖q y‖ ≤ r) :
    Continuous (fun y => inverseLog N (q y)) := by
  have hs : Summable (fun j : ℕ => r^(j+N+1)/(1-r)) := by
    have hh := ((hasSum_geometric_of_lt_one hr hR).mul_left (r^(N+1))).summable
    have he : Summable (fun j : ℕ => r^(j+N+1)) := by
      convert! hh using 1
      ext j
      rw [show j+N+1=j+(N+1) by omega, pow_add]
      ring
    exact he.div_const _
  apply Continuous.neg
  apply continuous_tsum (fun j => factor_continuous q hq (fun y => (hB y).trans_lt hR) _ (by omega)) hs
  intro j y
  apply (log_factor_bound N j (q y) ((hB y).trans_lt hR)).trans
  exact div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) (hB y) _)
    (by linarith : 0 < 1-r) (by linarith [hB y])

theorem tailLog_continuous (n : ℕ) (q : ℝ → ℂ) (r : ℝ)
    (hq : Continuous q) (hr : 0 ≤ r) (hR : r < 1) (hB : ∀ y, ‖q y‖ ≤ r) :
    Continuous (fun y => tailLog n (q y)) := by
  apply (inverseLog_continuous (5*n) q r hq hr hR hB).sub
  apply inverseLog_continuous n (fun y => (q y)^5) (r^5) (hq.pow 5) (by positivity)
    (pow_lt_one₀ hr hR (by norm_num))
  intro y
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hB y) _

theorem tail_continuous (n : ℕ) (q : ℝ → ℂ) (r : ℝ)
    (hq : Continuous q) (hr : 0 ≤ r) (hR : r < 1) (hB : ∀ y, ‖q y‖ ≤ r) :
    Continuous (fun y => EndpointFiniteConnection.tail n (q y)) := by
  have he := (tailLog_continuous n q r hq hr hR hB).cexp
  exact he.congr (fun y => exp_tailLog n (q y) ((hB y).trans_lt hR))

def root (j : Fin 4) (v y : ℝ) : ℂ :=
  FivePoleCircle.zeta^(j.val+1)*exp (-coordinate v y)

theorem root_continuous (j : Fin 4) (v : ℝ) : Continuous (root j v) := by
  unfold root coordinate
  fun_prop

theorem root_norm (j : Fin 4) (v y : ℝ) : ‖root j v y‖=Real.exp (-v) := by
  exact EndpointEtaTailBound.root_radius j v y

theorem root_tail_continuous (n : ℕ) (j : Fin 4) (v : ℝ) (hv : 0 < v) :
    Continuous (fun y => EndpointFiniteConnection.tail n (root j v y)) := by
  apply tail_continuous n (root j v) (Real.exp (-v)) (root_continuous j v)
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  intro y
  exact (root_norm j v y).le

end
end Borwein.EndpointTailContinuity
