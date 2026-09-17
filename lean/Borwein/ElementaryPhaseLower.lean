import Borwein.AngleDeficit
import Borwein.CombinedPhaseSign

set_option autoImplicit false

namespace Borwein.ElementaryPhaseLower
noncomputable section
open PhaseAngleRange ExplicitPhaseProfile ElementaryPhaseConstants CombinedPhaseSign

def lower (a : ℕ) (τ : ℝ) : ℝ :=
  if a = 0 then 3 else if a = 1 then 9/10 else if a = 2 then 7/10 else
    if a = 3 then (7/10)*(Real.exp (-τ)/(1+Real.exp (-τ))) else
      (17/20)*(Real.exp (-τ)/(1+Real.exp (-τ)))

theorem sine_small (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi/10) :
    (49/50:ℝ)*x ≤ Real.sin x := by
  have hx : x ≤ (8/25:ℝ) := by linarith [Real.pi_lt_d2]
  have hs := pow_le_pow_left₀ hx0 hx 2
  have hc := mul_le_mul_of_nonneg_right hs hx0
  have ht := Real.sin_ge_sub_cube hx0
  nlinarith

theorem cosine_small (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi/10) :
    (9/10:ℝ) ≤ Real.cos x := by
  have hx : x ≤ (8/25:ℝ) := by linarith [Real.pi_lt_d2]
  have hs := pow_le_pow_left₀ hx0 hx 2
  have ht := Real.one_sub_sq_div_two_le_cos (x := x)
  nlinarith

theorem cosine_three_tenths : (7/12:ℝ) ≤ Real.cos (3*Real.pi/10) := by
  have he : 3*Real.pi/10 = Real.pi/2-Real.pi/5 := by ring
  rw [he,Real.cos_pi_div_two_sub]
  have ht := Real.sin_ge_sub_cube (by positivity : (0:ℝ) ≤ Real.pi/5)
  have hx : Real.pi/5 ≤ (16/25:ℝ) := by linarith [Real.pi_lt_d2]
  have hx3 := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ Real.pi/5) hx 3
  nlinarith [Real.pi_gt_d2]

theorem cosine_lower (x b L : ℝ) (hx : 0 ≤ x) (hxb : x ≤ b) (hb : b ≤ Real.pi)
    (hL : L ≤ Real.cos b) : L ≤ Real.cos x :=
  hL.trans (Real.cos_le_cos_of_nonneg_of_le_pi hx hb hxb)

theorem strong_zero (τ : ℝ) (hτ : 0 ≤ τ) : (3:ℝ) ≤ phase 0 τ := by
  have h := angle_ranges τ hτ
  have hu := cosine_small _ h.1.1 h.1.2.le
  have hv := cosine_small _ h.2.1 h.2.2.le
  have hm := mul_le_mul hu hv (by norm_num : (0:ℝ) ≤ 9/10) (by linarith)
  norm_num [phase]
  nlinarith

theorem strong_one (τ : ℝ) (hτ : 0 ≤ τ) : (9/10:ℝ) ≤ -phase 1 τ := by
  have h := angle_ranges τ hτ
  have hp := Real.pi_pos
  have hu := cosine_lower (2*Real.pi/5-(alpha τ+2*beta τ)/5) (2*Real.pi/5) (3/10)
    (by linarith [h.1.2]) (by linarith [h.1.1]) (by linarith) cosine_second.1
  have hv := cosine_lower (Real.pi/5-(2*alpha τ-beta τ)/5) (Real.pi/5) (4/5)
    (by linarith [h.2.2]) (by linarith [h.2.1]) (by linarith) cosine_first.1
  have hm := mul_le_mul hu hv (by norm_num : (0:ℝ) ≤ 4/5) (by linarith)
  have he1 : 3*Real.pi*(1:ℝ)/5+(alpha τ+2*beta τ)/5 =
      Real.pi-(2*Real.pi/5-(alpha τ+2*beta τ)/5) := by ring
  have he2 : -Real.pi*(1:ℝ)/5+(2*alpha τ-beta τ)/5 =
      -(Real.pi/5-(2*alpha τ-beta τ)/5) := by ring
  unfold phase
  norm_num only [Nat.cast_one]
  rw [he1,he2,Real.cos_pi_sub,Real.cos_neg]
  nlinarith

theorem strong_two (τ : ℝ) (hτ : 0 ≤ τ) : (7/10:ℝ) ≤ -phase 2 τ := by
  have h := angle_ranges τ hτ
  have hp := Real.pi_pos
  have hu := cosine_lower (Real.pi/5+(alpha τ+2*beta τ)/5) (3*Real.pi/10) (7/12)
    (by linarith [h.1.1]) (by linarith [h.1.2]) (by linarith) cosine_three_tenths
  have hv := cosine_lower (2*Real.pi/5-(2*alpha τ-beta τ)/5) (2*Real.pi/5) (3/10)
    (by linarith [h.2.2]) (by linarith [h.2.1]) (by linarith) cosine_second.1
  have hm := mul_le_mul hu hv (by norm_num : (0:ℝ) ≤ 3/10) (by linarith)
  have he1 : 3*Real.pi*(2:ℝ)/5+(alpha τ+2*beta τ)/5 =
      (Real.pi/5+(alpha τ+2*beta τ)/5)+Real.pi := by ring
  have he2 : -Real.pi*(2:ℝ)/5+(2*alpha τ-beta τ)/5 =
      -(2*Real.pi/5-(2*alpha τ-beta τ)/5) := by ring
  unfold phase
  norm_num only [Nat.cast_ofNat]
  rw [he1,he2,Real.cos_add_pi,Real.cos_neg]
  nlinarith

theorem weak_three (τ : ℝ) (hτ : 0 ≤ τ) :
    (7/10:ℝ)*(Real.exp (-τ)/(1+Real.exp (-τ))) ≤ -phase 3 τ := by
  have h := angle_ranges τ hτ
  have hd := (AngleDeficit.actual_deficits τ hτ).2
  have hp := Real.pi_pos
  have hq : 0 ≤ Real.exp (-τ)/(1+Real.exp (-τ)) := by positivity
  have hc := cosine_lower (Real.pi/5-(alpha τ+2*beta τ)/5) (Real.pi/5) (4/5)
    (by linarith [h.1.2]) (by linarith [h.1.1]) (by linarith) cosine_first.1
  have hs := sine_small (Real.pi/10-(2*alpha τ-beta τ)/5)
    (by linarith [h.2.2]) (by linarith [h.2.1])
  have hs' : (49/50:ℝ)*((6/25)*(Real.exp (-τ)/(1+Real.exp (-τ)))) ≤
      Real.sin (Real.pi/10-(2*alpha τ-beta τ)/5) := by linarith
  have hm := mul_le_mul hc hs' (by positivity) (by linarith)
  rw [weak_three_identity]
  nlinarith

theorem weak_four (τ : ℝ) (hτ : 0 ≤ τ) :
    (17/20:ℝ)*(Real.exp (-τ)/(1+Real.exp (-τ))) ≤ -phase 4 τ := by
  have h := angle_ranges τ hτ
  have hd := (AngleDeficit.actual_deficits τ hτ).1
  have hp := Real.pi_pos
  have hq : 0 ≤ Real.exp (-τ)/(1+Real.exp (-τ)) := by positivity
  have hc := cosine_lower (Real.pi/5+(2*alpha τ-beta τ)/5) (3*Real.pi/10) (7/12)
    (by linarith [h.2.1]) (by linarith [h.2.2]) (by linarith) cosine_three_tenths
  have hs := sine_small (Real.pi/10-(alpha τ+2*beta τ)/5)
    (by linarith [h.1.2]) (by linarith [h.1.1])
  have hs' : (49/50:ℝ)*((2/5)*(Real.exp (-τ)/(1+Real.exp (-τ)))) ≤
      Real.sin (Real.pi/10-(alpha τ+2*beta τ)/5) := by linarith
  have hm := mul_le_mul hs' hc (by norm_num : (0:ℝ) ≤ 7/12) (by linarith)
  rw [weak_four_identity]
  nlinarith

theorem lower_pos (a : ℕ) (τ : ℝ) : 0 < lower a τ := by
  unfold lower
  split_ifs <;> positivity

theorem signed_phase_lower (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    lower a τ ≤ sign a*phase a τ := by
  interval_cases a
  · simpa [lower,sign] using strong_zero τ hτ
  · simpa [lower,sign] using strong_one τ hτ
  · simpa [lower,sign] using strong_two τ hτ
  · simpa [lower,sign] using weak_three τ hτ
  · simpa [lower,sign] using weak_four τ hτ

end
end Borwein.ElementaryPhaseLower
