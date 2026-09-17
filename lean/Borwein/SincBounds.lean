import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic

namespace Borwein.SincBounds
noncomputable section

theorem cos_le_quartic (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24 := by
  let f (t : ℝ) := 1-t^2/2+t^4/24-Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t-t+t^3/6 := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have h := Real.sin_ge_sub_cube (show 0 ≤ t from (interior_subset ht))
    linarith
  have h := hm (by simp) hx hx
  dsimp [f] at h
  simp only [Real.cos_zero] at h
  linarith

theorem sin_le_quintic (x : ℝ) (hx : 0 ≤ x) :
    Real.sin x ≤ x-x^3/6+x^5/120 := by
  let f (t : ℝ) := t-t^3/6+t^5/120-Real.sin t
  have hd (t : ℝ) : deriv f t = 1-t^2/2+t^4/24-Real.cos t := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have h := cos_le_quartic t (interior_subset ht)
    linarith
  have h := hm (by simp) hx hx
  dsimp [f] at h
  simp only [Real.sin_zero, sub_zero] at h
  linarith

def profile (a : ℝ) := a^2/6-a^4/120

theorem profile_le_gap (v : ℝ) (hv : 0 ≤ v) :
    profile v ≤ 1-Real.sinc v := by
  obtain rfl | hp := hv.eq_or_lt
  · norm_num [profile]
  rw [Real.sinc_of_ne_zero hp.ne']
  have h := (div_le_div_iff_of_pos_right hp).mpr (sin_le_quintic v hp.le)
  have he : (v-v^3/6+v^5/120)/v = 1-profile v := by
    unfold profile
    field_simp
    ring
  rw [he] at h
  linarith

theorem profile_mono (a v : ℝ) (ha : 0 ≤ a) (hav : a ≤ v) (hv : v ≤ 3) :
    profile a ≤ profile v := by
  have hv0 := le_trans ha hav
  have ha3 := le_trans hav hv
  have hsq : a^2 ≤ v^2 := pow_le_pow_left₀ ha hav 2
  have hv9 : v^2 ≤ 9 := by nlinarith
  have ha9 : a^2 ≤ 9 := le_trans hsq hv9
  have h := mul_nonneg (sub_nonneg.mpr hsq) (show 0 ≤ 20-v^2-a^2 by linarith)
  unfold profile
  nlinarith

theorem profile_le_eight_fifteenths (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) :
    profile a ≤ 8/15 := by
  have h := profile_mono a 2 ha ha2 (by norm_num)
  norm_num [profile] at h ⊢
  exact h

theorem global_lower (a v : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) (hav : a ≤ |v|) :
    a^2/6-a^4/120 ≤ 1-Real.sinc v := by
  have he : Real.sinc |v| = Real.sinc v := by
    rcases le_or_gt 0 v with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.sinc_neg]
  change profile a ≤ 1-Real.sinc v
  rw [← he]
  by_cases hv3 : |v| ≤ 3
  · exact le_trans (profile_mono a |v| ha hav hv3) (profile_le_gap |v| (abs_nonneg v))
  · have hp : 0 < |v| := by linarith [abs_nonneg v]
    have hs := Real.sinc_le_inv_abs (show |v| ≠ 0 from hp.ne')
    rw [abs_abs] at hs
    have hi : |v|⁻¹ ≤ (1:ℝ)/3 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (le_of_lt (lt_of_not_ge hv3))
    have hb := profile_le_eight_fifteenths a ha ha2
    linarith


theorem inverse_lower (s v : ℝ) (hs : 0 < s) (hv : s ≤ |v|) :
    1-1/s ≤ 1-Real.sinc v := by
  have hp : 0 < |v| := lt_of_lt_of_le hs hv
  have h := Real.sinc_le_inv_abs (abs_pos.mp hp)
  have hi : |v|⁻¹ ≤ 1/s := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le hs hv
  linarith

theorem strengthened_lower (s v : ℝ) (hs : 0 < s) (hv : s ≤ |v|) :
    max (profile (min 2 s)) (1-1/s) ≤ 1-Real.sinc v := by
  apply max_le
  · exact global_lower _ _ (le_min (by norm_num) hs.le) (min_le_left _ _)
      (le_trans (min_le_right _ _) hv)
  · exact inverse_lower s v hs hv

end
end Borwein.SincBounds


