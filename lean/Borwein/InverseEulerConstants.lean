import Borwein.SincBounds
import Mathlib.Analysis.Complex.Exponential

set_option autoImplicit false

namespace Borwein.InverseEulerConstants
noncomputable section

theorem radial_numerator (x : ℝ) (hx : 0 ≤ x) :
    2*(1-Real.exp (-x)) ≤ x*(1+Real.exp (-x)) := by
  let f (t : ℝ) := t*(1+Real.exp (-t))-2*(1-Real.exp (-t))
  have hd (t : ℝ) : deriv f t = 1-(1+t)*Real.exp (-t) := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have he := mul_le_mul_of_nonneg_right (Real.add_one_le_exp t) (Real.exp_pos (-t)).le
    rw [← Real.exp_add] at he
    simp only [add_neg_cancel, Real.exp_zero] at he
    nlinarith
  have he := hm (by simp) hx hx
  dsimp [f] at he
  simp only [neg_zero, Real.exp_zero] at he
  linarith

theorem symmetric_exp (x : ℝ) (hx : 0 ≤ x) (hX : x ≤ 2/25) :
    Real.exp x + Real.exp (-x) - 2 ≤ (1001/1000)*x^2 := by
  have ha : |x| ≤ 1 := by rw [abs_of_nonneg hx]; linarith
  have hb : |-x| ≤ 1 := by simpa using ha
  have hp := Real.exp_bound ha (show 0 < (4:ℕ) by norm_num)
  have hn := Real.exp_bound hb (show 0 < (4:ℕ) by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hx, abs_neg] at hp hn
  have hp' := (abs_le.mp hp).2
  have hn' := (abs_le.mp hn).2
  have hs : x^2 ≤ 4/625 := by nlinarith
  have ht := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hs)
  nlinarith

theorem cosine_gap (t : ℝ) (ht : |t| ≤ 1/10) :
    (499/1000)*t^2 ≤ 1-Real.cos t := by
  have hc := SincBounds.cos_le_quartic |t| (abs_nonneg t)
  rw [Real.cos_abs, sq_abs] at hc
  have h4 : |t|^4 = t^4 := by
    calc
      _ = (|t|^2)^2 := by ring
      _ = (t^2)^2 := by rw [sq_abs]
      _ = _ := by ring
  rw [h4] at hc
  have hs : t^2 ≤ 1/100 := by nlinarith [sq_abs t, abs_nonneg t]
  have he := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hs)
  nlinarith

theorem twelve_frequency_budget :
    (11/20:ℝ) ≤ (359/1000)*∑ l ∈ Finset.range 12, 1/((l+1:ℕ):ℝ)^2 := by
  norm_num [Finset.sum_range_succ]

end
end Borwein.InverseEulerConstants
