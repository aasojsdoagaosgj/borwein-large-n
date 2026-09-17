import Borwein.EndpointSignedRadialLoss

set_option autoImplicit false

namespace Borwein.EndpointOuterNumericBudget
noncomputable section
open Set EndpointGaussianIntegral

def damped (t : ℝ) : ℝ := t^3*Real.exp (-t)

theorem damped_deriv (t : ℝ) : HasDerivAt damped (t^2*Real.exp (-t)*(3-t)) t := by
  have hi := hasDerivAt_id t
  convert! (hi.pow 3).mul hi.neg.exp using 1 <;>
    simp only [damped, Pi.pow_apply, Pi.neg_apply, id_eq] <;> ring

theorem damped_antitone : AntitoneOn damped (Ici 3) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 3)
    (continuous_iff_continuousAt.mpr (fun t => (damped_deriv t).continuousAt)).continuousOn
    (fun t _ => (damped_deriv t).differentiableAt.differentiableWithinAt)
  intro t ht
  have h3 : 3 ≤ t := interior_subset ht
  rw [(damped_deriv t).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)

theorem large_exponential : (100000000000:ℝ) ≤ Real.exp (1000/39) := by
  have hh := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 1000/39) 32
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  linarith

theorem damped_base : 27000*damped (1000/39) ≤ (1/200:ℝ) := by
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 100000000000) large_exponential
  have hh := mul_le_mul_of_nonneg_left hi (by norm_num : (0:ℝ) ≤ 27000*(1000/39)^3)
  unfold damped
  rw [Real.exp_neg]
  norm_num only [one_div] at hh
  nlinarith

theorem decay_uniform (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) :
    Real.exp (-1/(30*v))/v^3 ≤ (1/200:ℝ) := by
  have ht : (1000/39:ℝ) ≤ 1/(30*v) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hd := damped_antitone (show (1000/39:ℝ) ∈ Ici 3 by norm_num)
    (show 1/(30*v) ∈ Ici 3 by change 3 ≤ 1/(30*v); linarith) ht
  have hh := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 27000)
  have he : Real.exp (-1/(30*v))/v^3=27000*damped (1/(30*v)) := by
    unfold damped
    rw [neg_div]
    ring
  rw [he]
  exact hh.trans damped_base

theorem small_exponential (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) : Real.exp (v/6) ≤ (21/20:ℝ) := by
  have hh := Real.exp_bound (x := (1/100:ℝ)) (by norm_num : |(1/100:ℝ)| ≤ 1) (by norm_num : 0 < (3:ℕ))
  norm_num [Finset.sum_range_succ, Nat.factorial] at hh
  have hu := (abs_le.mp hh).2
  have he := Real.exp_le_exp.mpr (show v/6 ≤ (1/100:ℝ) by linarith)
  linarith

theorem normalizer_lower (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) : v^2 ≤ normalizer n v := by
  have hJ := EndpointGaussianBudget.normalizer_lower n v hn hv hτ
  have hs := Real.sq_sqrt hv.le
  have hp := Real.sqrt_nonneg v
  have hvs : v ≤ Real.sqrt v := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hvs (by positivity : 0 ≤ (61/20)*v)
  nlinarith

theorem prefactor_bound (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    (12*Real.pi*Real.exp (v/6))/(v*normalizer n v) ≤ 40/v^3 := by
  have hJ := EndpointGaussianIntegral.normalizer_pos n v hn hv
  have hL := normalizer_lower n v hn hv hV hτ
  have hE := small_exponential v hv hV
  have hP : 12*Real.pi*Real.exp (v/6) ≤ 40 := by
    have hh := mul_le_mul_of_nonneg_left hE (by positivity : 0 ≤ 12*Real.pi)
    nlinarith [Real.pi_lt_d2]
  apply (div_le_div_iff₀ (mul_pos hv hJ) (pow_pos hv 3)).mpr
  have h1 := mul_le_mul_of_nonneg_right hP (pow_nonneg hv.le 3)
  have h2 := mul_le_mul_of_nonneg_left hL (by positivity : 0 ≤ 40*v)
  nlinarith

theorem outer_budget (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ((12*Real.pi*Real.exp (v/6))/(v*normalizer n v))*Real.exp (-1/(30*v)) ≤ (1/5:ℝ) := by
  have hh := mul_le_mul_of_nonneg_right (prefactor_bound n v hn hv hV hτ) (Real.exp_pos (-1/(30*v))).le
  have hd := mul_le_mul_of_nonneg_left (decay_uniform v hv hV) (by norm_num : (0:ℝ) ≤ 40)
  calc
    _ ≤ (40/v^3)*Real.exp (-1/(30*v)) := hh
    _ = 40*(Real.exp (-1/(30*v))/v^3) := by ring
    _ ≤ _ := by linarith

end
end Borwein.EndpointOuterNumericBudget
