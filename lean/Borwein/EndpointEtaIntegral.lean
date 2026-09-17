import Borwein.EndpointEtaExponentialBudget
import Borwein.EndpointPolynomialContinuity

set_option autoImplicit false

namespace Borwein.EndpointEtaIntegral
noncomputable section
open Complex MeasureTheory Set EndpointPhaseAtoms EndpointGaussianIntegral
  EndpointMainArcConnection EndpointEtaExponentialBudget

def strongIntegral (a n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  EndpointStrongPolynomial.strongEta a n (coordinate v y)*exp ((k:ℂ)*coordinate v y)
def weakIntegral (a n : ℕ) (k v : ℝ) : ℂ := ∫ y in -(width v)..width v,
  EndpointWeakPolynomial.etaRemainder a n (coordinate v y)*
    exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y)

theorem strong_integral_bound (a n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖strongIntegral a n k v‖ ≤ 60*‖center n k v‖*Real.exp (-(9/10)/v) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(width v)) (b := width v)
    (f := fun y => EndpointStrongPolynomial.strongEta a n (coordinate v y)*exp ((k:ℂ)*coordinate v y))
    (C := (40/v)*‖center n k v‖*Real.exp (-(9/10)/v)) (by
      intro y hy
      rw [uIoc_of_le (by unfold width; linarith : -(width v) ≤ width v)] at hy
      exact strong_pointwise a n k v y hn hv hV (abs_le.mpr ⟨hy.1.le,hy.2⟩) hτ)
  apply hh.trans_eq
  have he : |width v-(-(width v))|=3*v/2 := by unfold width; rw [abs_of_pos (by linarith)]; ring
  rw [he]
  field_simp
  <;> ring

theorem weak_integral_bound (a n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖weakIntegral a n k v‖ ≤ 60*‖center n k v‖*Real.exp (-(9/10)/v) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(width v)) (b := width v)
    (f := fun y => EndpointWeakPolynomial.etaRemainder a n (coordinate v y)*exp (((k+((5*n:ℕ):ℝ):ℝ):ℂ)*coordinate v y))
    (C := (40/v)*‖center n k v‖*Real.exp (-(9/10)/v)) (by
      intro y hy
      rw [uIoc_of_le (by unfold width; linarith : -(width v) ≤ width v)] at hy
      exact weak_pointwise a n k v y hn hv hV (abs_le.mpr ⟨hy.1.le,hy.2⟩) hτ)
  apply hh.trans_eq
  have he : |width v-(-(width v))|=3*v/2 := by unfold width; rw [abs_of_pos (by linarith)]; ring
  rw [he]
  field_simp
  <;> ring

theorem small_exponential (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) :
    Real.exp (-(9/10)/v) ≤ v^3/100 := by
  let t : ℝ := (9/10)/v
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hh := Real.sum_le_exp_of_nonneg ht 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  have hT : t^5/120 ≤ Real.exp t := by
    nlinarith [pow_nonneg ht 3, pow_nonneg ht 4, sq_nonneg t]
  have hL : 100/v^3 ≤ t^5/120 := by
    dsimp [t]
    rw [div_pow, div_div]
    apply (div_le_div_iff₀ (pow_pos hv 3) (by positivity : 0 < v^5*120)).mpr
    have hs : 12000*v^2 ≤ (9/10:ℝ)^5 := by nlinarith
    have hp := mul_le_mul_of_nonneg_right hs (pow_nonneg hv.le 3)
    nlinarith
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 100/v^3) (hL.trans hT)
  rw [neg_div, Real.exp_neg]
  simpa only [one_div, inv_div, inv_inv] using hi

theorem normalized_budget (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    60*Real.exp (-(9/10)/v) ≤ v*normalizer n v := by
  have he := small_exponential v hv hV
  have hJ := EndpointGaussianBudget.normalizer_lower n v hn hv hτ
  have hs := Real.sq_sqrt hv.le
  have hp := Real.sqrt_nonneg v
  have hvs : v ≤ Real.sqrt v := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hvs (by positivity : 0 ≤ (61/20)*v)
  have hl : v^2 ≤ normalizer n v := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hl hv.le
  nlinarith

theorem ratio_bound (n : ℕ) (k v : ℝ) (z c : ℂ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hc : ‖center n k v‖ ≤ ‖c‖)
    (hz : ‖z‖ ≤ 60*‖center n k v‖*Real.exp (-(9/10)/v)) :
    ‖z/(c*(normalizer n v:ℂ))‖ ≤ v := by
  have hJ := normalizer_pos n v hn hv
  have hC : 0 < ‖c‖ := (norm_pos_iff.mpr (center_ne_zero n k v)).trans_le hc
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hJ.le]
  apply (div_le_iff₀ (mul_pos hC hJ)).mpr
  calc
    _ ≤ 60*‖center n k v‖*Real.exp (-(9/10)/v) := hz
    _ = ‖center n k v‖*(60*Real.exp (-(9/10)/v)) := by ring
    _ ≤ ‖center n k v‖*(v*normalizer n v) :=
      mul_le_mul_of_nonneg_left (normalized_budget n v hn hv hV hτ) (norm_nonneg _)
    _ ≤ ‖c‖*(v*normalizer n v) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

theorem strong_ratio_bound (a : Fin 3) (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖strongIntegral a.val n k v/(EndpointRootCancellation.constant a.val*center n k v*(normalizer n v:ℂ))‖ ≤ v := by
  apply ratio_bound n k v _ _ hn hv hV hτ _ (strong_integral_bound a.val n k v hn hv hV hτ)
  rw [norm_mul]
  have hh := EndpointStrongConstants.constant_norm_lower a
  nlinarith [norm_nonneg (center n k v)]

theorem weak_ratio_bound (a n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖weakIntegral a n k v/((-center n k v)*(normalizer n v:ℂ))‖ ≤ v := by
  apply ratio_bound n k v _ _ hn hv hV hτ _ (weak_integral_bound a n k v hn hv hV hτ)
  simp only [norm_neg, le_refl]

end
end Borwein.EndpointEtaIntegral
