import Borwein.InverseEulerGeometry

set_option autoImplicit false

namespace Borwein.InverseEulerNearLoss
noncomputable section
open InverseEulerLoss InverseEulerGeometry InverseEulerConstants PeriodicRadialProfile

theorem scaled_loss (x t d c : ℝ) (hx : 0 < x) (hX : x ≤ 2/25)
    (hd : 0 < d) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hcd : c*(1001/1000+2*d) ≤ 2*d)
    (hD : d*x^2 ≤ 1-Real.cos t) :
    c ≤ x*geometricLoss (ray x t) := by
  let r := Real.exp (-x)
  let D := 1-Real.cos t
  let E := Real.exp x+Real.exp (-x)-2+2*D
  have hr : 0 < 1-r := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hD0 : 0 < D := lt_of_lt_of_le (mul_pos hd (sq_pos_of_pos hx)) hD
  have hE0 : 0 < E := by
    dsimp [E]
    linarith [Real.add_one_le_exp x, Real.add_one_le_exp (-x)]
  have hEu : E ≤ (1001/1000)*x^2+2*D := by
    dsimp [E]
    linarith [symmetric_exp x hx.le hX]
  have hcx := mul_le_mul_of_nonneg_right hcd (sq_nonneg x)
  have hdd := mul_le_mul_of_nonneg_left hD (show 0 ≤ 2*(1-c) by linarith)
  have hce : c*E ≤ 2*D := by
    have he := mul_le_mul_of_nonneg_left hEu hc
    nlinarith
  have hrad : 2*(1-r) ≤ x*(1+r) := radial_numerator x hx.le
  have h1 := mul_le_mul_of_nonneg_left hce hr.le
  have h2 := mul_le_mul_of_nonneg_right hrad hD0.le
  rw [ray_loss x t hx]
  change c ≤ x*((1+r)/(1-r)*(D/E))
  rw [show x*((1+r)/(1-r)*(D/E)) = x*(1+r)*D/((1-r)*E) by
    simp only [div_eq_mul_inv, mul_inv_rev]; ring]
  apply (le_div_iff₀ (mul_pos hr hE0)).mpr
  nlinarith

theorem near_scaled_loss (x t : ℝ) (hx : 0 < x) (hX : x ≤ 2/25)
    (ht : |t| ≤ 1/10) (hl : 3*x/4 ≤ |t|) :
    (359/1000:ℝ) ≤ x*geometricLoss (ray x t) := by
  have hs : (9/16)*x^2 ≤ t^2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hD : (4491/16000)*x^2 ≤ 1-Real.cos t := by
    nlinarith [cosine_gap t ht]
  exact scaled_loss x t (4491/16000) (359/1000) hx hX (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hD

theorem far_scaled_loss (x t : ℝ) (hx : 0 < x) (hX : x ≤ 13/2000)
    (ht : |t| ≤ Real.pi) (hl : 6*x/5 ≤ |t|) :
    (11/20:ℝ) ≤ x*geometricLoss (ray x t) := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (show 0 ≤ 6*x/5 by positivity) ht hl
  rw [Real.cos_abs] at hc
  have hg := cosine_gap (6*x/5) (by rw [abs_of_nonneg (by positivity)]; linarith)
  have hD : (8982/12500)*x^2 ≤ 1-Real.cos t := by nlinarith
  exact scaled_loss x t (8982/12500) (11/20) hx (by linarith) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hD

theorem near_frequency_lower (u t : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000)
    (hl : 3*u/4 ≤ |t|) (ht : |t| ≤ 6*u/5) (l : ℕ) (hL : l < 12) :
    (359/1000)/(u*(l+1:ℝ)^2) ≤ frequencyLoss (ray u t) l := by
  have hk : (0:ℝ) < l+1 := by positivity
  have hku : (l+1:ℝ) ≤ 12 := by exact_mod_cast hL
  have he := near_scaled_loss ((l+1:ℝ)*u) ((l+1:ℝ)*t) (by positivity)
    (by nlinarith) (by rw [abs_mul, abs_of_pos hk]; nlinarith)
    (by rw [abs_mul, abs_of_pos hk]; nlinarith)
  have hp : ray u t^(l+1) = ray ((l+1:ℝ)*u) ((l+1:ℝ)*t) := by
    simpa [ray] using ray_power u t (l+1)
  rw [frequencyLoss, hp]
  apply (le_div_iff₀ hk).mpr
  have he' : (359/1000)/((l+1:ℝ)*u) ≤
      geometricLoss (ray ((l+1:ℝ)*u) ((l+1:ℝ)*t)) :=
    (div_le_iff₀ (mul_pos hk hu)).mpr (by nlinarith)
  calc
    (359/1000)/(u*(l+1:ℝ)^2)*(l+1:ℝ) = (359/1000)/((l+1:ℝ)*u) := by
      field_simp
      <;> ring
    _ ≤ _ := he'

theorem principal_loss (u t : ℝ) (hu : 0 < u) (hU : u ≤ 13/2000)
    (hl : 3*u/4 ≤ |t|) (ht : |t| ≤ Real.pi) :
    (11/20)/u ≤ totalLoss (ray u t) := by
  have hq : ‖ray u t‖ < 1 := by
    rw [ray_norm]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  by_cases hnear : |t| ≤ 6*u/5
  · have hf := finite_loss_le (ray u t) hq (Finset.range 12)
    have hs := Finset.sum_le_sum (fun l (hl' : l ∈ Finset.range 12) =>
      near_frequency_lower u t hu hU hl hnear l (Finset.mem_range.mp hl'))
    have hid : (∑ l ∈ Finset.range 12, (359/1000)/(u*(l+1:ℝ)^2)) =
        ((359/1000)*∑ l ∈ Finset.range 12, 1/((l+1:ℕ):ℝ)^2)/u := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro l _
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hid] at hs
    exact (div_le_div_of_nonneg_right twelve_frequency_budget hu.le).trans (hs.trans hf)
  · have he := far_scaled_loss u t hu hU ht (by linarith)
    have hf := finite_loss_le (ray u t) hq ({0}:Finset ℕ)
    simp [frequencyLoss] at hf
    exact ((div_le_iff₀ hu).mpr (by nlinarith)).trans hf

end
end Borwein.InverseEulerNearLoss
