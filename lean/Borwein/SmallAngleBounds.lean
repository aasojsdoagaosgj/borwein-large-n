import Borwein.SineCertificate

namespace Borwein.SmallAngleBounds
noncomputable section

theorem sin_two_fifths : Real.sin (2/5:ℝ) ≤ 39/100 := by
  have h := SineCertificate.polynomial_error (2/5) (by norm_num)
  have hp : SineCertificate.polynomial (2/5)+(2:ℝ)^24/(23:ℕ).factorial ≤ 39/100 := by
    norm_num [SineCertificate.polynomial,Finset.sum_range_succ,Nat.factorial]
  have ha := (abs_le.mp h).2
  linarith

theorem abs_sine_upper (v : ℝ) (hv : |v| ≤ 2/5) : |Real.sin v| ≤ 39/100 := by
  have hp := Real.pi_gt_d2
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith)]
  apply le_trans _ sin_two_fifths
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg v]) (by linarith) hv

theorem cosine_nonnegative (v : ℝ) (hv : |v| ≤ 2/5) : 0 ≤ Real.cos v := by
  have hp := Real.pi_gt_d2
  have ha := abs_le.mp hv
  exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [ha.1],by linarith [ha.2]⟩

theorem cosine_upper_outer (v : ℝ) (hv0 : 367/1000 ≤ |v|) (hv1 : |v| ≤ 2/5) :
    Real.cos v ≤ 467/500 := by
  have ht0 : 0 ≤ |v|/2 := by positivity
  have ht1 : |v|/2 ≤ 1/5 := by linarith
  have hp := pow_le_pow_left₀ ht0 ht1 3
  have hs := Real.sin_ge_sub_cube ht0
  have hl : (1093/6000:ℝ) ≤ Real.sin (|v|/2) := by norm_num at hp; linarith
  have he := Real.cos_two_mul_eq_one_sub (|v|/2)
  have hc : Real.cos v = Real.cos |v| := by
    rcases le_total 0 v with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,Real.cos_neg]
  rw [show 2*(|v|/2)=|v| by ring,← hc] at he
  have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1093/6000) hl 2
  nlinarith

theorem perturbed_real_budget (r s v : ℝ) (hr : r ≤ 3091/10000) (hs : |s| ≤ 9511/10000)
    (hv : |v| ≤ 2/5) : r*Real.cos v-s*Real.sin v ≤ 33/50 := by
  have hcos0 := cosine_nonnegative v hv
  have hm : r*Real.cos v ≤ (3091/10000:ℝ)*Real.cos v := mul_le_mul_of_nonneg_right hr hcos0
  have hneg : -(s*Real.sin v) ≤ |s| * |Real.sin v| := by
    simpa only [abs_mul] using neg_le_abs (s*Real.sin v)
  by_cases hsmall : |v| ≤ 367/1000
  · have hsin := (Real.abs_sin_le_abs (x := v)).trans hsmall
    have hprod := mul_le_mul hs hsin (abs_nonneg (Real.sin v)) (by norm_num : (0:ℝ) ≤ 9511/10000)
    have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one v) (by norm_num : (0:ℝ) ≤ 3091/10000)
    linarith
  · have hsin := abs_sine_upper v hv
    have hprod := mul_le_mul hs hsin (abs_nonneg (Real.sin v)) (by norm_num : (0:ℝ) ≤ 9511/10000)
    have hcos := mul_le_mul_of_nonneg_left (cosine_upper_outer v (le_of_not_ge hsmall) hv)
      (by norm_num : (0:ℝ) ≤ 3091/10000)
    linarith

end
end Borwein.SmallAngleBounds
