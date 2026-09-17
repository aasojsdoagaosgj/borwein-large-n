import Borwein.EndpointPositiveKernel

set_option autoImplicit false

namespace Borwein.EndpointPositiveFinite
noncomputable section
open Complex EndpointPositiveKernel EndpointPhaseAtoms EndpointActualPhase EndpointTailGlobalLog
  EndpointEtaExponentialBudget EndpointMainArcConnection EndpointRadialNormalization

def value (n : ℕ) (v y : ℝ) : ℂ :=
  Polynomial.eval₂ (Int.castRingHom ℂ) (point v y) (Borwein.polynomial n)
def difference (n : ℕ) (v y : ℝ) : ℂ := value n v y-EndpointEta.G (point v y)

theorem value_eq (n : ℕ) (v y : ℝ) (hv : 0 < v) :
    value n v y=EndpointEta.G (point v y)*EndpointFiniteConnection.tail n (point v y) :=
  EndpointFiniteConnection.polynomial_eq_G_tail n (point v y) (point_norm_lt_one v y hv)

theorem difference_eq (n : ℕ) (v y : ℝ) (hv : 0 < v) :
    difference n v y=EndpointEta.G (point v y)*(EndpointFiniteConnection.tail n (point v y)-1) := by
  rw [difference, value_eq n v y hv]
  ring

theorem tail_error (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖EndpointFiniteConnection.tail n (point v y)-1‖ ≤ (radialX n v/v)*Real.exp (radialX n v/v) :=
  endpoint_tail_bound n _ v hn hv hV hτ (point_norm v y)

theorem G_coarse_norm (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) :
    ‖EndpointEta.G (point v y)‖ ≤ 40*Real.exp (A/v-v/6)*Real.exp (-1/v) := by
  have hh := G_norm v y hv hV hy
  have hp : 0 < Real.exp (A/v-v/6)*Real.exp (-1/v) := by positivity
  nlinarith

theorem strong_pointwise (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖value n v y*exp ((k:ℂ)*coordinate v y)‖ ≤ (40/v)*‖center n k v‖*Real.exp (-(9/10)/v) := by
  rw [value_eq n v y hv, norm_mul, norm_mul, coefficient_norm]
  have hG := G_coarse_norm v y hv hV hy
  have ht := tail_error n v y hn hv hV hτ
  have hh := norm_add_le (EndpointFiniteConnection.tail n (point v y)-1) (1:ℂ)
  simp only [sub_add_cancel, norm_one] at hh
  have hT : ‖EndpointFiniteConnection.tail n (point v y)‖ ≤ Real.exp (radialX n v/v)/v := by
    have hs := strong_tail_envelope n v hv hV hτ
    linarith
  calc
    _ ≤ (40*Real.exp (A/v-v/6)*Real.exp (-1/v))*(Real.exp (radialX n v/v)/v)*Real.exp (k*v) := by gcongr
    _ = (40/v)*(Real.exp (A/v-v/6)*Real.exp (-1/v)*Real.exp (radialX n v/v)*Real.exp (k*v)) := by ring
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (exponential_budget n k v hn hv hτ) (by positivity : 0 ≤ 40/v)
      simpa only [mul_assoc] using hb

theorem weak_pointwise (n : ℕ) (k v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖difference n v y*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)‖ ≤
      (40/v)*‖center n k v‖*Real.exp (-(9/10)/v) := by
  rw [difference_eq n v y hv, norm_mul, norm_mul, coefficient_norm]
  have hG := G_coarse_norm v y hv hV hy
  have ht := tail_error n v y hn hv hV hτ
  have hp := radialX_positive n v
  calc
    _ ≤ (40*Real.exp (A/v-v/6)*Real.exp (-1/v))*((radialX n v/v)*Real.exp (radialX n v/v))*Real.exp ((k+((5*n:ℕ):ℝ))*v) := by gcongr
    _ = (40/v)*(Real.exp (A/v-v/6)*Real.exp (-1/v)*Real.exp (radialX n v/v)*
        (radialX n v*Real.exp ((k+((5*n:ℕ):ℝ))*v))) := by ring
    _ = (40/v)*(Real.exp (A/v-v/6)*Real.exp (-1/v)*Real.exp (radialX n v/v)*Real.exp (k*v)) := by rw [weak_shift]
    _ ≤ _ := by
      have hb := mul_le_mul_of_nonneg_left (exponential_budget n k v hn hv hτ) (by positivity : 0 ≤ 40/v)
      simpa only [mul_assoc] using hb

end
end Borwein.EndpointPositiveFinite
