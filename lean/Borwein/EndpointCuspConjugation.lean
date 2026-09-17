import Borwein.EndpointEtaTwo

set_option autoImplicit false

namespace Borwein.EndpointCuspConjugation
noncomputable section
open Complex EndpointEta EndpointEtaMobius EndpointCuspTransfer EndpointEtaTwo
open scoped Real ComplexConjugate

theorem euler_conj (z : ℂ) (hz : ‖z‖ < 1) : euler (conj z) = conj (euler z) := by
  have he := (ModularForm.multipliable_one_sub_pow hz).map_tprod (starRingEnd ℂ) continuous_star
  simpa only [euler, map_sub, map_one, map_pow] using he.symm

theorem G_conj (z : ℂ) (hz : ‖z‖ < 1) : G (conj z) = conj (G z) := by
  have hz5 : ‖z^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by norm_num)
  unfold G
  rw [euler_conj z hz, ← map_pow, euler_conj (z^5) hz5, map_div₀]

theorem q_conj (z : ℂ) : conj (q z) = q (-conj z) := by
  unfold q
  rw [← Complex.exp_conj]
  congr 1
  simp [map_ofNat] <;> ring

theorem q_norm_lt_one (z : ℂ) (hz : 0 < z.im) : ‖q z‖ < 1 := by
  exact UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z,hz⟩

theorem reflect_cusp (l d : ℝ) (k : ℂ)
    (h : ∀ s : ℂ, 0 < s.im → G (q ((s+l)/5)) = k*exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-d)/5))/euler (q (-1/s))))
    (s : ℂ) (hs : 0 < s.im) :
    G (q ((s+(5-l:ℝ))/5)) = conj k*exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-(5-d:ℝ))/5))/euler (q (-1/s))) := by
  let t : ℂ := -conj s
  have ht : 0 < t.im := by simpa [t] using hs
  have htl : 0 < ((t+l)/5).im := by simpa using div_pos ht (by norm_num : (0:ℝ)<5)
  have htv := inverse_upper t ht
  have htd : 0 < ((-1/t-d)/5).im := by simpa using div_pos htv (by norm_num : (0:ℝ)<5)
  have hq0 : conj (q ((t+l)/5)) = q ((s+(5-l:ℝ))/5) := by
    rw [q_conj]
    have he : (s+(5-l:ℝ))/5 = -conj ((t+l)/5)+1 := by simp [t, map_ofNat, neg_div, one_div]; ring
    rw [he, q_add_one]
  have hqv : conj (q (-1/t)) = q (-1/s) := by
    rw [q_conj]
    congr 1
    simp [t, map_ofNat, neg_div, one_div]
  have hqd : conj (q ((-1/t-d)/5)) = q ((-1/s-(5-d:ℝ))/5) := by
    rw [q_conj]
    have he : -conj ((-1/t-d)/5) = (-1/s-(5-d:ℝ))/5+1 := by simp [t, map_ofNat, neg_div, one_div]; ring
    rw [he, q_add_one]
  have hm : conj (exp ((Real.pi:ℂ)*I*(t+1/t)/15)) = exp ((Real.pi:ℂ)*I*(s+1/s)/15) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [t, map_ofNat, neg_div, one_div] <;> ring
  have he := congrArg conj (h t ht)
  rw [← G_conj _ (q_norm_lt_one _ htl), hq0] at he
  simp only [map_mul, map_div₀] at he
  rw [hm, ← euler_conj _ (q_norm_lt_one _ htd), ← euler_conj _ (q_norm_lt_one _ htv), hqd, hqv] at he
  exact he

theorem G_cusp_three (s : ℂ) (hs : 0 < s.im) :
    G (q ((s+3)/5)) = exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-2)/5))/euler (q (-1/s))) := by
  have he := reflect_cusp 2 3 1 (fun z hz => by simpa using G_cusp_two z hz) s hs
  norm_num at he
  simpa only [one_div] using he

theorem G_cusp_four (s : ℂ) (hs : 0 < s.im) :
    G (q ((s+4)/5)) = exp ((Real.pi:ℂ)*I/5)*exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-4)/5))/euler (q (-1/s))) := by
  have he := reflect_cusp 1 1 (exp (-(Real.pi:ℂ)*I/5))
    (fun z hz => by simpa using G_cusp_one z hz) s hs
  have hk : conj (exp (-(Real.pi:ℂ)*I/5)) = exp ((Real.pi:ℂ)*I/5) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  simpa only [hk, show (5:ℝ)-1=4 by norm_num, Complex.ofReal_ofNat] using he

end
end Borwein.EndpointCuspConjugation
