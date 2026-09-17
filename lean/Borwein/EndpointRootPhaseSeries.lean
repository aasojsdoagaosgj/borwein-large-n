import Borwein.EndpointRootLinear

set_option autoImplicit false

namespace Borwein.EndpointRootPhaseSeries
noncomputable section
open Complex EndpointTailMain

/-- The coefficient in the root phase, including its logarithmic divisor. -/
def coefficient (ξ : ℂ) (k : ℕ) : ℂ :=
  if 5 ∣ k then 0 else (ξ^k/(1-ξ^k)+1/2)/(k:ℂ)

theorem root_kernel_bound (ξ : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1) :
    ‖ξ/(1-ξ)+1/2‖ ≤ 1 := by
  have hr := FifthRootCoordinates.real_upper ξ hξ hne
  have hs := FifthRootCoordinates.coordinate_square ξ hξ
  have hd : 1 ≤ ‖1-ξ‖ := by
    have he := Complex.sq_norm (1-ξ)
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im] at he
    nlinarith [norm_nonneg (1-ξ)]
  have he : ξ/(1-ξ)+1/2 = (1+ξ)/(2*(1-ξ)) := by
    field_simp
    ring
  rw [he, norm_div, norm_mul]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by positivity : 0 < 2*‖1-ξ‖)).mpr
  have ht := norm_add_le (1:ℂ) ξ
  rw [norm_one, FiveRootProductExpansion.root_norm ξ hξ] at ht
  linarith

theorem coefficient_bound (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (k : ℕ) :
    ‖coefficient ξ k‖ ≤ 1/(k:ℝ) := by
  by_cases hk : 5 ∣ k
  · simp only [coefficient, if_pos hk, norm_zero]
    positivity
  · have hp : (ξ^k)^5=1 := by rw [← pow_mul, Nat.mul_comm k 5, pow_mul, hξ.pow_eq_one, one_pow]
    have hn : ξ^k ≠ 1 := fun he => hk ((hξ.pow_eq_one_iff_dvd k).mp he)
    simp only [coefficient, if_neg hk, norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (root_kernel_bound (ξ^k) hp hn) (Nat.cast_nonneg k)

theorem term_eq (ξ x : ℂ) (k : ℕ) : phaseTerm ξ x k = coefficient ξ k*x^k := by
  unfold phaseTerm coefficient
  split_ifs <;> ring

theorem term_bound (ξ x : ℂ) (hξ : IsPrimitiveRoot ξ 5) (k : ℕ) :
    ‖phaseTerm ξ x k‖ ≤ ‖x‖^k/(k:ℝ) := by
  rw [term_eq, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_right (coefficient_bound ξ hξ k) (pow_nonneg (norm_nonneg x) k)).trans_eq (by ring)

theorem phase_summable (ξ x : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hx : ‖x‖ < 1) :
    Summable (phaseTerm ξ x) := by
  apply (summable_geometric_of_lt_one (norm_nonneg x) hx).of_norm_bounded
  intro k
  by_cases hk : k=0
  · subst k; simp [phaseTerm]
  · exact (term_bound ξ x hξ k).trans ((div_le_self (pow_nonneg (norm_nonneg x) k)
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)))

theorem phase_bound (ξ x : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hx : ‖x‖ < 1) :
    ‖phase ξ x‖ ≤ ‖x‖/(1-‖x‖) := by
  have he := (phase_summable ξ x hξ hx).sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, phaseTerm, dvd_zero, if_true, zero_add] at he
  change (∑' k : ℕ, phaseTerm ξ x (k+1)) = phase ξ x at he
  rw [← he]
  have hg : HasSum (fun k : ℕ => ‖x‖^(k+1)) (‖x‖/(1-‖x‖)) := by
    simpa [pow_succ, div_eq_mul_inv, mul_comm] using
      (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖
  apply tsum_of_norm_bounded hg
  intro k
  exact (term_bound ξ x hξ (k+1)).trans (div_le_self (by positivity) (by exact_mod_cast Nat.le_add_left 1 k))

theorem linear_remainder (ξ x : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hx : ‖x‖ < 1) :
    ‖phase ξ x-coefficient ξ 1*x‖ ≤ (‖x‖^2/2)/(1-‖x‖) := by
  have he := (phase_summable ξ x hξ hx).sum_add_tsum_nat_add 2
  have hsum : (∑ k ∈ Finset.range 2, phaseTerm ξ x k) = coefficient ξ 1*x := by
    norm_num [Finset.sum_range_succ, phaseTerm, coefficient]
    ring
  rw [hsum] at he
  change coefficient ξ 1*x+(∑' k : ℕ, phaseTerm ξ x (k+2)) = phase ξ x at he
  rw [← he, add_sub_cancel_left]
  have hg : HasSum (fun k : ℕ => ‖x‖^(k+2)/2) ((‖x‖^2/2)/(1-‖x‖)) := by
    have hh : HasSum (fun k : ℕ => (‖x‖^2/2)*‖x‖^k)
        ((‖x‖^2/2)*(1-‖x‖)⁻¹) :=
      (hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x‖^2/2)
    rw [← div_eq_mul_inv] at hh
    apply hh.congr_fun
    intro k
    rw [pow_add]
    ring
  apply tsum_of_norm_bounded hg
  intro k
  exact (term_bound ξ x hξ (k+2)).trans
    (div_le_div_of_nonneg_left (by positivity) (by norm_num) (by exact_mod_cast Nat.le_add_left 2 k))

theorem exponential_linear_remainder (ξ x : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hx : ‖x‖ ≤ 1/10) :
    ‖exp (phase ξ x)-1-coefficient ξ 1*x‖ ≤ 2*‖x‖^2 := by
  have hx1 : ‖x‖ < 1 := by linarith
  have hd : 0 < 1-‖x‖ := by linarith
  have hp : ‖phase ξ x‖ ≤ (10/9)*‖x‖ := by
    apply (phase_bound ξ x hξ hx1).trans
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (norm_nonneg x) (sub_nonneg.mpr hx)]
  have hr : ‖phase ξ x-coefficient ξ 1*x‖ ≤ (5/9)*‖x‖^2 := by
    apply (linear_remainder ξ x hξ hx1).trans
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr hx)]
  have he := Complex.norm_exp_sub_one_sub_id_le (x := phase ξ x) (by nlinarith)
  have ht := norm_add_le (exp (phase ξ x)-1-phase ξ x) (phase ξ x-coefficient ξ 1*x)
  have hid : (exp (phase ξ x)-1-phase ξ x)+(phase ξ x-coefficient ξ 1*x) =
      exp (phase ξ x)-1-coefficient ξ 1*x := by ring
  rw [hid] at ht
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (10/9)*‖x‖)).mpr hp
  nlinarith [sq_nonneg ‖x‖]

end
end Borwein.EndpointRootPhaseSeries
