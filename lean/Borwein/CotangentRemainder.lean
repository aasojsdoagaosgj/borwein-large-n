import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

namespace Borwein.CotangentRemainder
noncomputable section
open Complex

theorem unit_disk_integerComplement (x : ℂ) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    x ∈ Complex.integerComplement := by
  rw [Complex.mem_integerComplement_iff]
  rintro ⟨a,ha⟩
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact hx0 ha.symm
  have hn : (1:ℝ) ≤ |(a:ℝ)| := by exact_mod_cast Int.one_le_abs ha0
  have he : ‖(a:ℂ)‖ = |(a:ℝ)| := by simp
  rw [ha] at he
  linarith

theorem denominator_lower (x : ℂ) (n : ℕ) :
    (1-‖x‖^2)*((n+1:ℕ):ℝ)^2 ≤ ‖x^2-((n+1:ℕ):ℂ)^2‖ := by
  have ht := norm_sub_norm_le (((n+1:ℕ):ℂ)^2) (x^2)
  rw [norm_sub_rev] at ht
  simp only [norm_pow,Complex.norm_natCast] at ht
  have ha : (1:ℝ) ≤ ((n+1:ℕ):ℝ)^2 := by
    have h : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr ha)]

theorem term_bound (x : ℂ) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) (n : ℕ) :
    ‖cotTerm x n‖ ≤ (2*‖x‖/(1-‖x‖^2))*(1/((n+1:ℕ):ℝ)^2) := by
  have hc := unit_disk_integerComplement x hx0 hx
  have hd : 0 < 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have he : cotTerm x n = 2*x/(x^2-((n+1:ℕ):ℂ)^2) := by
    rw [cotTerm_identity hc]
    push_cast
    congr 1
    ring
  rw [he,norm_div,norm_mul,Complex.norm_ofNat]
  have hb := div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ 2*‖x‖)
    (by positivity : 0 < (1-‖x‖^2)*((n+1:ℕ):ℝ)^2) (denominator_lower x n)
  convert! hb using 1
  field_simp

theorem reciprocal_square_sum :
    HasSum (fun n : ℕ => 1/((n+1:ℕ):ℝ)^2) (Real.pi^2/6) := by
  have h := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  simpa using h

theorem cotangent_bound (x : ℂ) (hx0 : x ≠ 0) (hx : ‖x‖ < 1) :
    ‖(Real.pi:ℂ)*Complex.cot ((Real.pi:ℂ)*x)-1/x‖ ≤
      Real.pi^2*‖x‖/(3*(1-‖x‖^2)) := by
  have hc := unit_disk_integerComplement x hx0 hx
  have hs := summable_cotTerm hc
  have hb := reciprocal_square_sum.mul_left (2*‖x‖/(1-‖x‖^2))
  rw [cot_series_rep' hc]
  change ‖∑' n : ℕ, cotTerm x n‖ ≤ _
  have ht := (norm_tsum_le_tsum_norm hs.norm).trans
    (Summable.tsum_le_tsum (fun n => term_bound x hx0 hx n) hs.norm hb.summable)
  rw [hb.tsum_eq] at ht
  convert! ht using 1
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end Borwein.CotangentRemainder
