import Borwein.EndpointGaussianIntegral

set_option autoImplicit false

namespace Borwein.EndpointGaussianBudget
noncomputable section
open EndpointGaussianIntegral EndpointSaddleIdentification EndpointDerivativeConstants

theorem normalizer_square (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    variance n v*(normalizer n v)^2=2*Real.pi := by
  have hV : 0 < variance n v := quadratic_positive n v hn hv
  rw [normalizer, Real.sq_sqrt (by positivity)]
  field_simp

theorem normalizer_lower (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : (61/20)*v*Real.sqrt v ≤ normalizer n v := by
  have hV : 0 < variance n v := quadratic_positive n v hn hv
  have hJ := normalizer_pos n v hn hv
  have hs := Real.sq_sqrt hv.le
  have hU := (second_main_bounds n v hn hv hτ).2
  have hx : ((61/20)*v*Real.sqrt v)^2=(3721/400)*v^3 := by
    simp only [mul_pow, hs]
    ring
  have hc : variance n v*((61/20)*v*Real.sqrt v)^2 ≤ variance n v*(normalizer n v)^2 := by
    rw [hx, normalizer_square n v hn hv]
    have hh := mul_le_mul_of_nonneg_left hU (by norm_num : (0:ℝ) ≤ 3721/400)
    change v^3*variance n v ≤ _ at hU
    nlinarith [Real.pi_gt_d2]
  have hh : ((61/20)*v*Real.sqrt v)^2 ≤ (normalizer n v)^2 := by
    by_contra h
    exact (not_lt_of_ge hc) (mul_lt_mul_of_pos_left (lt_of_not_ge h) hV)
  have hp : 0 ≤ (61/20)*v*Real.sqrt v := by positivity
  nlinarith

theorem local_error_ratio (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    (1280000/28227:ℝ)*v^2/normalizer n v ≤ (149/10)*Real.sqrt v := by
  apply (div_le_iff₀ (normalizer_pos n v hn hv)).mpr
  have hh := mul_le_mul_of_nonneg_left (normalizer_lower n v hn hv hτ)
    (by positivity : 0 ≤ (149/10)*Real.sqrt v)
  have he : (149/10)*Real.sqrt v*((61/20)*v*Real.sqrt v)=(9089/200)*v^2 := by
    have hs := Real.sq_sqrt hv.le
    calc
      _ = (9089/200)*v*(Real.sqrt v)^2 := by ring
      _ = _ := by rw [hs]; ring
  rw [he] at hh
  exact (mul_le_mul_of_nonneg_right (by norm_num : (1280000/28227:ℝ) ≤ 9089/200) (sq_nonneg v)).trans hh

theorem tail_rate (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : 1/(10*v) ≤ (variance n v/2)*(width v)^2 := by
  have hb := (second_main_bounds n v hn hv hτ).1
  change (38/100:ℝ) ≤ v^3*variance n v at hb
  apply (div_le_iff₀ (by positivity : 0 < 10*v)).mpr
  unfold width
  nlinarith

theorem small_exponential (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) :
    Real.exp (-1/(10*v)) ≤ v := by
  have hx : 0 ≤ 1/(10*v) := by positivity
  have hh := Real.sum_le_exp_of_nonneg hx 3
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  have hc : 1/v ≤ 1/(200*v^2) := one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have he : 1/(200*v^2)=(1/(10*v))^2/2 := by ring
  rw [he] at hc
  have hl : 1/v ≤ Real.exp (1/(10*v)) := by
    have heX : (1:ℝ)/(10*v)=v⁻¹*(1/10) := by ring
    rw [heX] at hc ⊢
    nlinarith
  have hi := one_div_le_one_div_of_le (by positivity : 0 < 1/v) hl
  rw [neg_div, Real.exp_neg]
  simpa only [one_div, inv_inv] using hi

theorem tail_ratio (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    Real.exp (-(variance n v/2)*(width v)^2) ≤ (1/10)*Real.sqrt v := by
  have hh : Real.exp (-(variance n v/2)*(width v)^2) ≤ Real.exp (-1/(10*v)) := by
    apply Real.exp_le_exp.mpr
    have hr := tail_rate n v hn hv hτ
    rw [neg_div]
    nlinarith
  apply (hh.trans (small_exponential v hv hV)).trans
  have hs := Real.sq_sqrt hv.le
  have hp := Real.sqrt_nonneg v
  nlinarith

theorem gaussian_budget (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖localIntegral n v/(normalizer n v:ℂ)-1‖ ≤ 15*Real.sqrt v := by
  have hh := normalized_gaussian_bound n v hn hv hτ
  have h1 := local_error_ratio n v hn hv hτ
  have h2 := tail_ratio n v hn hv hV hτ
  linarith

end
end Borwein.EndpointGaussianBudget
