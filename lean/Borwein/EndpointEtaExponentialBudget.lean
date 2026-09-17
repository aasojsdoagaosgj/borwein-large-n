import Borwein.EndpointRadialNormalization

set_option autoImplicit false

namespace Borwein.EndpointEtaExponentialBudget
noncomputable section
open Complex EndpointPhaseAtoms EndpointActualPhase EndpointTailGlobalLog
  EndpointRadialNormalization EndpointMainArcConnection

theorem strong_tail_envelope (n : ℕ) (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    1+(radialX n v/v)*Real.exp (radialX n v/v) ≤ Real.exp (radialX n v/v)/v := by
  have hX := radialX_small n v hτ
  have hp := radialX_positive n v
  have hE : 1 ≤ Real.exp (radialX n v/v) := Real.one_le_exp (by positivity)
  apply (le_div_iff₀ hv).mpr
  have hc : v+radialX n v ≤ 1 := by linarith
  have hh := mul_le_mul_of_nonneg_right hc (Real.exp_pos (radialX n v/v)).le
  have hi := mul_le_mul_of_nonneg_left hE hv.le
  have he : ((radialX n v/v)*Real.exp (radialX n v/v))*v=radialX n v*Real.exp (radialX n v/v) := by field_simp
  nlinarith

theorem coefficient_norm (k v y : ℝ) : ‖exp ((k:ℂ)*coordinate v y)‖=Real.exp (k*v) := by
  rw [Complex.norm_exp]
  simp [coordinate]

theorem weak_shift (n : ℕ) (k v : ℝ) :
    radialX n v*Real.exp ((k+((5*n:ℕ):ℝ))*v)=Real.exp (k*v) := by
  unfold radialX
  rw [← Real.exp_add]
  congr 1
  ring

theorem exponential_budget (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    Real.exp (A/v-v/6)*Real.exp (-1/v)*Real.exp (radialX n v/v)*Real.exp (k*v) ≤
      ‖center n k v‖*Real.exp (-(9/10)/v) := by
  rw [center_norm n k v hn hv, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hl := radial_loss n v hn hv hτ
  have hX := radialX_small n v hτ
  have he : radialX n v/v ≤ (1/200)/v := div_le_div_of_nonneg_right hX hv.le
  have hr : A/v-v/6+-1/v+radialX n v/v+k*v-
      ((n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v)+k*v-v/6+-(9/10)/v) =
      (A/v-(n:ℝ)*PhaseIntegral.radialR (((5*n:ℕ):ℝ)*v))+radialX n v/v-(1/10)/v := by ring
  have hz : 1/(100*v)+(1/200)/v ≤ (1/10)/v := by
    have hh := div_le_div_of_nonneg_right (by norm_num : (3/200:ℝ) ≤ 1/10) hv.le
    convert! hh using 1 <;> ring
  linarith

theorem strong_pointwise (a n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖EndpointStrongPolynomial.strongEta a n (coordinate v y)*exp ((k:ℂ)*coordinate v y)‖ ≤
      (40/v)*‖center n k v‖*Real.exp (-(9/10)/v) := by
  rw [norm_mul, coefficient_norm]
  have h0 := EndpointStrongPolynomial.strong_eta_bound a n v y hn hv hV hy hτ
  have h1 := strong_tail_envelope n v hv hV hτ
  have hX := radialX_positive n v
  have h2 := main_norm_bound v y hv
  have hp := mul_le_mul_of_nonneg_right h0 (Real.exp_pos (k*v)).le
  have hh : 40*‖EndpointRootAsymptotic.main (coordinate v y)‖*Real.exp (-1/v)*
      (1+(radialX n v/v)*Real.exp (radialX n v/v))*Real.exp (k*v) ≤
      (40/v)*(Real.exp (A/v-v/6)*Real.exp (-1/v)*Real.exp (radialX n v/v)*Real.exp (k*v)) := by
    calc
      _ ≤ 40*Real.exp (A/v-v/6)*Real.exp (-1/v)*(Real.exp (radialX n v/v)/v)*Real.exp (k*v) := by
        gcongr <;> positivity
      _ = _ := by ring
  exact (hp.trans hh).trans (by
    have hb := mul_le_mul_of_nonneg_left (exponential_budget n k v hn hv hτ) (by positivity : 0 ≤ 40/v)
    simpa only [mul_assoc] using hb)

theorem weak_pointwise (a n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖EndpointWeakPolynomial.etaRemainder a n (coordinate v y)*
      exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)‖ ≤
      (40/v)*‖center n k v‖*Real.exp (-(9/10)/v) := by
  rw [norm_mul, coefficient_norm]
  have h0 := EndpointEtaTailBound.eta_remainder_bound a n v y hn hv hV hy hτ
  have hp := mul_le_mul_of_nonneg_right h0 (Real.exp_pos ((k+((5*n:ℕ):ℝ))*v)).le
  have h2 := main_norm_bound v y hv
  have hh : 40*‖EndpointRootAsymptotic.main (coordinate v y)‖*Real.exp (-1/v)*
      ((radialX n v/v)*Real.exp (radialX n v/v))*Real.exp ((k+((5*n:ℕ):ℝ))*v) ≤
      (40/v)*(Real.exp (A/v-v/6)*Real.exp (-1/v)*Real.exp (radialX n v/v)*Real.exp (k*v)) := by
    calc
      _ = (40/v)*(‖EndpointRootAsymptotic.main (coordinate v y)‖*Real.exp (-1/v)*Real.exp (radialX n v/v)*
          (radialX n v*Real.exp ((k+((5*n:ℕ):ℝ))*v))) := by ring
      _ = (40/v)*(‖EndpointRootAsymptotic.main (coordinate v y)‖*Real.exp (-1/v)*Real.exp (radialX n v/v)*Real.exp (k*v)) := by rw [weak_shift]
      _ ≤ _ := by gcongr
  exact (hp.trans hh).trans (by
    have hb := mul_le_mul_of_nonneg_left (exponential_budget n k v hn hv hτ) (by positivity : 0 ≤ 40/v)
    simpa only [mul_assoc] using hb)

end
end Borwein.EndpointEtaExponentialBudget
