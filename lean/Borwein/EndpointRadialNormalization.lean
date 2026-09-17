import Borwein.EndpointLocalNumericBudget

set_option autoImplicit false

namespace Borwein.EndpointRadialNormalization
noncomputable section
open Complex EndpointPhaseAtoms EndpointPhaseSeries EndpointPhaseDerivatives EndpointActualPhase
  EndpointTailGlobalLog EndpointMainArcConnection

theorem radialX_positive (n : ℕ) (v : ℝ) : 0 < radialX n v := Real.exp_pos _

theorem radialX_small (n : ℕ) (v : ℝ) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : radialX n v ≤ 1/200 := by
  have hh := EndpointDerivativeConstants.exponential_lower.trans (Real.exp_le_exp.mpr hτ)
  have hl : (200:ℝ) ≤ Real.exp (((5*n:ℕ):ℝ)*v) := by linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 200) hl
  simpa [radialX, neg_mul, Real.exp_neg, one_div] using hi

theorem correction_norm (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : ‖q0 n v y‖ ≤ radialX n v/(v*(1-radialX n v)) := by
  have hr := radialX_positive n v
  have hR : radialX n v < 1 := lt_of_le_of_lt (radialX_small n v hτ) (by norm_num)
  have hg : HasSum (fun k : ℕ => (radialX n v)^(k+1)/v) (radialX n v/(v*(1-radialX n v))) := by
    convert! ((hasSum_geometric_of_lt_one hr.le hR).mul_left (radialX n v)).div_const v using 1
    · ext k
      rw [pow_succ]
      ring
    · field_simp
      <;> ring
  have hs : HasSum (fun k : ℕ => component n 0 0 v y (k+1)) (q0 n v y) := by
    have hh := (hasSum_nat_add_iff' 1).mpr (component_summable n 0 0 v y hn hv).hasSum
    simpa [q0, series, component, coefficient, Finset.sum_range_succ] using hh
  have hb : ∀ k : ℕ, ‖component n 0 0 v y (k+1)‖ ≤ (radialX n v)^(k+1)/v := by
    intro k
    have hh := component_bound n 0 0 v y (k+1) hv
    simp only [pow_zero, pow_one, one_mul] at hh
    rw [geometric_identity] at hh
    simpa only [Nat.zero_add, pow_one, radialX] using hh
  rw [← hs.tsum_eq]
  exact (norm_tsum_le_tsum_norm hs.summable.norm).trans
    ((hs.summable.norm.tsum_le_tsum hb hg.summable).trans_eq hg.tsum_eq)

theorem correction_small (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : ‖q0 n v y‖ ≤ 1/(100*v) := by
  apply (correction_norm n v y hn hv hτ).trans
  have hr := radialX_positive n v
  have hs := radialX_small n v hτ
  have hR : 0 < 1-radialX n v := by linarith
  apply (div_le_div_iff₀ (by positivity : 0 < v*(1-radialX n v)) (by positivity : 0 < 100*v)).mpr
  nlinarith

theorem radial_loss (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    A/v-(n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v) ≤ 1/(100*v) := by
  have he := EndpointSaddleIdentification.radial_f0_value n v hn hv
  have heR := congrArg Complex.re he
  have hf : (f0 n v 0).re=A/v+(q0 n v 0).re := by
    simp [f0, atom, coordinate, Complex.mul_re, Complex.normSq_apply]
    ring
  rw [hf] at heR
  simp only [Complex.ofReal_re] at heR
  have hb := (Complex.re_le_norm (-(q0 n v 0))).trans (by simpa only [norm_neg] using correction_small n v 0 hn hv hτ)
  rw [Complex.neg_re] at hb
  linarith

theorem main_norm_bound (v y : ℝ) (hv : 0 < v) :
    ‖EndpointRootAsymptotic.main (coordinate v y)‖ ≤ Real.exp (A/v-v/6) := by
  rw [EndpointRootAsymptotic.main, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have he : ((2*(Real.pi:ℂ)^2/75)/coordinate v y-coordinate v y/6).re =
      A*v/(v^2+y^2)-v/6 := by
    simp [A, coordinate, Complex.div_re, Complex.normSq_apply, ← Complex.ofReal_pow]
    ring
  rw [he]
  have hA : 0 ≤ A := by linarith [EndpointDerivativeConstants.A_bounds.1]
  have hh := div_le_div_of_nonneg_left (mul_nonneg hA hv.le)
    (by positivity : 0 < v^2) (by nlinarith : v^2 ≤ v^2+y^2)
  have hE : A*v/v^2=A/v := by field_simp
  rw [hE] at hh
  linarith

theorem center_norm (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    ‖center n k v‖=Real.exp ((n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)+k*v-v/6) := by
  rw [center_real n k v hn hv, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

end
end Borwein.EndpointRadialNormalization
