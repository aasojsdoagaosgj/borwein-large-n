import Borwein.ExponentialKernelRemainder

set_option autoImplicit false

namespace Borwein.WedgeExponentialKernel
noncomputable section
open Complex ExponentialKernelRemainder

theorem denominator_lower (x : ℂ) (hx : (x^2).re ≤ 0) (n : ℕ) :
    ((n+1:ℕ):ℝ)^2 ≤ ‖x^2-((n+1:ℕ):ℂ)^2‖ := by
  have ht := Complex.re_le_norm (((n+1:ℕ):ℂ)^2-x^2)
  have he : (((n+1:ℕ):ℂ)^2).re = ((n+1:ℕ):ℝ)^2 := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [Complex.sub_re, he, norm_sub_rev] at ht
  linarith

theorem cot_term_bound (x : ℂ) (hc : x ∈ Complex.integerComplement)
    (hx : (x^2).re ≤ 0) (n : ℕ) :
    ‖cotTerm x n‖ ≤ (2*‖x‖)*(1/((n+1:ℕ):ℝ)^2) := by
  have he : cotTerm x n = 2*x/(x^2-((n+1:ℕ):ℂ)^2) := by
    rw [cotTerm_identity hc]
    push_cast
    congr 1
    ring
  rw [he, norm_div, norm_mul, Complex.norm_ofNat]
  have hb := div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 2*‖x‖)
    (by positivity : 0 < ((n+1:ℕ):ℝ)^2) (denominator_lower x hx n)
  simpa only [div_eq_mul_inv, one_mul] using hb

theorem cotangent_bound (x : ℂ) (hc : x ∈ Complex.integerComplement) (hx : (x^2).re ≤ 0) :
    ‖(Real.pi:ℂ)*cot ((Real.pi:ℂ)*x)-1/x‖ ≤ Real.pi^2*‖x‖/3 := by
  have hs := summable_cotTerm hc
  have hb := CotangentRemainder.reciprocal_square_sum.mul_left (2*‖x‖)
  rw [cot_series_rep' hc]
  change ‖∑' n : ℕ, cotTerm x n‖ ≤ _
  have ht := (norm_tsum_le_tsum_norm hs.norm).trans
    (Summable.tsum_le_tsum (fun n => cot_term_bound x hc hx n) hs.norm hb.summable)
  rw [hb.tsum_eq] at ht
  have he : (2*‖x‖)*(Real.pi^2/6) = Real.pi^2*‖x‖/3 := by ring
  simpa only [he] using ht

theorem normalized_im (z : ℂ) : (normalized z).im = -z.re/(2*Real.pi) := by
  unfold normalized
  rw [div_mul_eq_div_div, Complex.div_I]
  rw [show (2:ℂ)*Real.pi = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl]
  simp only [Complex.neg_im, Complex.neg_re, Complex.mul_im, Complex.I_im, Complex.I_re,
    mul_one, mul_zero, add_zero, Complex.div_ofReal_re, neg_div]

theorem normalized_square_re (z : ℂ) :
    (normalized z^2).re = -(z^2).re/(4*Real.pi^2) := by
  have he : normalized z^2 = -(z^2)/((4*Real.pi^2:ℝ):ℂ) := by
    unfold normalized
    push_cast
    field_simp
    ring_nf
    simp [I_sq]
  rw [he, Complex.div_ofReal_re, Complex.neg_re]

theorem normalized_integerComplement (z : ℂ) (hz : 0 < z.re) :
    normalized z ∈ Complex.integerComplement := by
  have hn : (normalized z).im < 0 := by
    rw [normalized_im]
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨a,ha⟩
  have hh := congrArg Complex.im ha
  simp at hh
  linarith

theorem exp_ne_one (z : ℂ) (hz : 0 < z.re) : exp z ≠ 1 := by
  have hn : 1 < ‖exp z‖ := by rw [Complex.norm_exp]; exact Real.one_lt_exp_iff.mpr hz
  intro he
  rw [he, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem cotangent_identity (z : ℂ) (hz : 0 < z.re) :
    kernel z+1/2 = (-I/(2*(Real.pi:ℂ)))*
      ((Real.pi:ℂ)*cot ((Real.pi:ℂ)*normalized z)-1/normalized z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he : exp z-1 ≠ 0 := sub_ne_zero.mpr (exp_ne_one z hz)
  have he' : 1-exp z ≠ 0 := sub_ne_zero.mpr (exp_ne_one z hz).symm
  have hx : 2*(Real.pi:ℂ)*I*normalized z = z := by unfold normalized; field_simp
  rw [Complex.cot_pi_eq_exp_ratio, hx]
  unfold kernel normalized
  field_simp
  ring_nf
  simp [I_sq]
  ring

/-- No small-radius restriction: the square-real-part condition controls every pole. -/
theorem shifted_bound (z : ℂ) (hz : 0 < z.re) (hs : 0 ≤ (z^2).re) :
    ‖1/(exp z-1)-1/z+1/2‖ ≤ ‖z‖/12 := by
  have hx : (normalized z^2).re ≤ 0 := by
    rw [normalized_square_re]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hc := cotangent_bound (normalized z) (normalized_integerComplement z hz) hx
  have hb := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ 1/(2*Real.pi))
  change ‖kernel z+1/2‖ ≤ _
  rw [cotangent_identity z hz, norm_mul]
  have hn : ‖-I/(2*(Real.pi:ℂ))‖ = 1/(2*Real.pi) := by
    simp [Real.norm_of_nonneg Real.pi_pos.le]
  rw [hn]
  apply hb.trans_eq
  rw [normalized_norm]
  have hp := Real.pi_ne_zero
  field_simp
  ring

theorem wedge_bound (v y : ℝ) (hv : 0 < v) (hy : |y| ≤ 3*v/4) :
    ‖1/(exp ((v:ℂ)+(y:ℂ)*I)-1)-1/((v:ℂ)+(y:ℂ)*I)+1/2‖ ≤
      ‖(v:ℂ)+(y:ℂ)*I‖/12 := by
  apply shifted_bound
  · simpa using hv
  · have hy2 : |y|^2 ≤ (3*v/4)^2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hy
    rw [sq_abs] at hy2
    simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
      add_zero, mul_one]
    nlinarith

end
end Borwein.WedgeExponentialKernel
