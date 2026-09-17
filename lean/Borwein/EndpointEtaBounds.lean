import Borwein.EndpointPositiveCusp
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace Borwein.EndpointEtaBounds
noncomputable section
open Complex EndpointEta Filter
open scoped Topology

theorem euler_error (z : ℂ) (hz : ‖z‖ < 1) :
    ‖euler z-1‖ ≤ Real.exp (‖z‖/(1-‖z‖))-1 := by
  have hp := (ModularForm.multipliable_one_sub_pow hz).hasProd
  have hs : HasSum (fun j : ℕ => ‖z‖^(j+1)) (‖z‖/(1-‖z‖)) := by
    simpa [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_left ‖z‖
  have hleft : Tendsto (fun s : Finset ℕ => ‖(∏ j ∈ s, (1-z^(j+1)))-1‖)
      atTop (𝓝 ‖euler z-1‖) := (hp.sub tendsto_const_nhds).norm
  have hright : Tendsto (fun s : Finset ℕ => Real.exp (∑ j ∈ s, ‖z‖^(j+1))-1)
      atTop (𝓝 (Real.exp (‖z‖/(1-‖z‖))-1)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp hs).sub tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  exact Eventually.of_forall fun s => by
    simpa only [norm_neg, norm_pow, ← sub_eq_add_neg] using
      s.norm_prod_one_add_sub_one_le (fun j : ℕ => -z^(j+1))

theorem quotient_error (u v : ℂ) (a b : ℝ) (hb : b < 1)
    (hu : ‖euler u-1‖ ≤ a) (hv : ‖euler v-1‖ ≤ b) :
    ‖euler u/euler v-1‖ ≤ (a+b)/(1-b) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans hu
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hv
  have hden : 1-b ≤ ‖euler v‖ := by
    have ht := norm_sub_norm_le (1:ℂ) (euler v)
    rw [norm_one, norm_sub_rev] at ht
    linarith
  have hv0 : euler v ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by linarith) hden)
  have hnum : ‖euler u-euler v‖ ≤ a+b := by
    calc
      _ = ‖(euler u-1)-(euler v-1)‖ := by congr 1; ring
      _ ≤ ‖euler u-1‖+‖euler v-1‖ := norm_sub_le _ _
      _ ≤ a+b := add_le_add hu hv
  rw [div_sub_one hv0, norm_div]
  exact div_le_div₀ (by positivity) hnum (by linarith) hden

theorem euler_error_small (z : ℂ) (r : ℝ) (hr : r ≤ 1/10) (hz : ‖z‖ ≤ r) :
    ‖euler z-1‖ ≤ 5*r/2 := by
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hz1 : ‖z‖ < 1 := by linarith
  have ht0 : 0 ≤ ‖z‖/(1-‖z‖) := div_nonneg (norm_nonneg z) (by linarith)
  have ht : ‖z‖/(1-‖z‖) ≤ 5*r/4 := by
    calc
      _ ≤ r/(9/10) := div_le_div₀ hr0 hz (by norm_num) (by linarith)
      _ ≤ 5*r/4 := by linarith
  have ht1 : |‖z‖/(1-‖z‖)| ≤ 1 := by rw [abs_of_nonneg ht0]; linarith
  have he := Real.abs_exp_sub_one_le ht1
  rw [abs_of_nonneg ht0] at he
  exact (euler_error z hz1).trans ((le_abs_self _).trans (he.trans (by linarith)))

theorem quotient_error_small (u v : ℂ) (r : ℝ) (hr : r ≤ 1/10)
    (hu : ‖u‖ ≤ r) (hv : ‖v‖ ≤ r) :
    ‖euler u/euler v-1‖ ≤ 10*r := by
  have hr0 : 0 ≤ r := (norm_nonneg u).trans hu
  have hb : 5*r/2 < 1 := by linarith
  have he := quotient_error u v (5*r/2) (5*r/2) hb
    (euler_error_small u r hr hu) (euler_error_small v r hr hv)
  apply he.trans
  apply (div_le_iff₀ (by linarith : 0 < 1-5*r/2)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hr hr0]

theorem inverse_re_lower (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    16/(25*v) ≤ (1/((v:ℂ)+(y:ℂ)*I)).re := by
  have hy2 : |y|^2 ≤ (3*v/4)^2 := (sq_le_sq₀ (abs_nonneg y) (by positivity)).mpr hy
  rw [sq_abs] at hy2
  have hd : 0 < v^2+y^2 := by positivity
  have he : (1/((v:ℂ)+(y:ℂ)*I)).re = v/(v^2+y^2) := by
    simp [Complex.normSq_apply, pow_two]
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0 < 25*v) hd).mpr
  nlinarith

theorem transformed_norm (c v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4)
    (hc : 25/16 ≤ c) :
    ‖exp (-(c:ℂ)/((v:ℂ)+(y:ℂ)*I))‖ ≤ Real.exp (-1/v) := by
  have hr := inverse_re_lower v y hv hy
  have hc0 : 0 ≤ c := by linarith
  have hprod : 1/v ≤ c*(1/((v:ℂ)+(y:ℂ)*I)).re := by
    calc
      1/v = (25/16:ℝ)*(16/(25*v)) := by field_simp
      _ ≤ c*(16/(25*v)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ c*(1/((v:ℂ)+(y:ℂ)*I)).re := mul_le_mul_of_nonneg_left hr hc0
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have he : (-(c:ℂ)/((v:ℂ)+(y:ℂ)*I)).re =
      -c*(1/((v:ℂ)+(y:ℂ)*I)).re := by
    simp [div_eq_mul_inv]
  rw [he]
  rw [neg_div]
  linarith

theorem primitive_transformed_norm (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    ‖exp (-4*(Real.pi:ℂ)^2/(25*((v:ℂ)+(y:ℂ)*I)))‖ ≤ Real.exp (-1/v) := by
  have hc : (25/16:ℝ) ≤ 4*Real.pi^2/25 := by nlinarith [Real.pi_gt_d2]
  have he : -4*(Real.pi:ℂ)^2/(25*((v:ℂ)+(y:ℂ)*I)) =
      -((4*Real.pi^2/25:ℝ):ℂ)/((v:ℂ)+(y:ℂ)*I) := by
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact transformed_norm (4*Real.pi^2/25) v y hv hy hc

theorem small_exponential (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) :
    Real.exp (-1/v) ≤ 1/10 := by
  have ht : (10:ℝ) ≤ 1/v := (le_div_iff₀ hv).mpr (by linarith)
  have he : (10:ℝ) ≤ Real.exp (1/v) := by linarith [Real.add_one_le_exp (1/v)]
  rw [neg_div, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<10) he

/-- The positive-cusp correction satisfies the manuscript's exponentially small budget. -/
theorem positive_correction_error (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hy : |y| ≤ 3*v/4) :
    ‖euler (exp (-4*(Real.pi:ℂ)^2/((v:ℂ)+(y:ℂ)*I)))/
      euler (exp (-4*(Real.pi:ℂ)^2/(5*((v:ℂ)+(y:ℂ)*I))))-1‖ ≤
        10*Real.exp (-1/v) := by
  apply quotient_error_small _ _ _ (small_exponential v hv hV)
  · have hc : (25/16:ℝ) ≤ 4*Real.pi^2 := by nlinarith [Real.pi_gt_d2]
    convert transformed_norm (4*Real.pi^2) v y hv hy hc using 1 <;> push_cast <;> ring
  · have hc : (25/16:ℝ) ≤ 4*Real.pi^2/5 := by nlinarith [Real.pi_gt_d2]
    have he : -4*(Real.pi:ℂ)^2/(5*((v:ℂ)+(y:ℂ)*I)) =
        -((4*Real.pi^2/5:ℝ):ℂ)/((v:ℂ)+(y:ℂ)*I) := by
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    exact transformed_norm (4*Real.pi^2/5) v y hv hy hc

def positiveMain (w : ℂ) : ℂ :=
  (Real.sqrt 5:ℂ)*exp (-(2*(Real.pi:ℂ)^2/15)/w-w/6)

theorem positiveMain_ne_zero (w : ℂ) : positiveMain w ≠ 0 := by
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem normalized_positive_cusp (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hy : |y| ≤ 3*v/4) :
    ‖G (exp (-((v:ℂ)+(y:ℂ)*I)))/positiveMain ((v:ℂ)+(y:ℂ)*I)-1‖ ≤
      10*Real.exp (-1/v) := by
  have hw : 0 < ((v:ℂ)+(y:ℂ)*I).re := by simpa using hv
  rw [EndpointPositiveCusp.positive_cusp _ hw]
  change ‖(positiveMain ((v:ℂ)+(y:ℂ)*I)*
    (euler (exp (-4*(Real.pi:ℂ)^2/((v:ℂ)+(y:ℂ)*I)))/
      euler (exp (-4*(Real.pi:ℂ)^2/(5*((v:ℂ)+(y:ℂ)*I))))))/
        positiveMain ((v:ℂ)+(y:ℂ)*I)-1‖ ≤ _
  rw [mul_div_cancel_left₀ _ (positiveMain_ne_zero _)]
  exact positive_correction_error v y hv hV hy

end
end Borwein.EndpointEtaBounds
