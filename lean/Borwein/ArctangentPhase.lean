import Borwein.LogPhaseCoordinates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

set_option autoImplicit false

namespace Borwein.ArctangentPhase
noncomputable section
open LogPhaseCoordinates

theorem arg_right_half_plane (z : ℂ) (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im/z.re) := by
  have hb := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have h := Real.arctan_tan hb.1 hb.2
  rw [Complex.tan_arg] at h
  exact h.symm

theorem arctan_difference (a b q : ℝ) (hu : a^2+b^2 = 1)
    (ha : a < 1) (hb : 0 ≤ b) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.arctan (-b*q/(1-a*q))-Real.arctan (-b/(1-a)) =
      Real.arctan ((1-q)/(1+q)*(b/(1-a))) := by
  have ha0 : 0 < 1-a := by linarith
  have haq : a*q < 1 := by
    rcases le_total 0 a with ha' | ha'
    · have h := mul_le_mul_of_nonneg_left hq1 ha'
      linarith
    · have h := mul_nonpos_of_nonpos_of_nonneg ha' hq
      linarith
  have hqa : 0 < 1-a*q := by linarith
  have hqa' : 1-q*a ≠ 0 := by nlinarith
  have hqp : 1+q ≠ 0 := by positivity
  let u := -b*q/(1-a*q)
  let v := b/(1-a)
  have hu0 : u ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) hqa.le
  have hv0 : 0 ≤ v := div_nonneg hb ha0.le
  have huv : u*v < 1 := (mul_nonpos_of_nonpos_of_nonneg hu0 hv0).trans_lt (by norm_num)
  have hv : -b/(1-a) = -v := by dsimp [v]; ring
  change Real.arctan u-Real.arctan (-b/(1-a)) = _
  rw [hv,Real.arctan_neg,sub_neg_eq_add,Real.arctan_add huv]
  congr 1
  have hnum : u+v = b*(1-q)/((1-a*q)*(1-a)) := by
    dsimp [u,v]
    field_simp [ha0.ne',hqa.ne',hqa',hqp]
    ring
  have hden : 1-u*v = (1-a)*(1+q)/((1-a*q)*(1-a)) := by
    dsimp [u,v]
    field_simp [ha0.ne',hqa.ne',hqa',hqp]
    have huq := congrArg (fun t : ℝ => q*t) hu
    nlinarith
  rw [hnum,hden]
  field_simp [ha0.ne',hqa.ne',hqa',hqp] <;> ring

theorem argumentShift_arctan (ξ : ℂ) (hu : ξ.re^2+ξ.im^2 = 1)
    (hr : ξ.re < 1) (hi : 0 ≤ ξ.im) (τ : ℝ) (hτ : 0 ≤ τ) :
    argumentShift ξ τ = Real.arctan
      ((1-Real.exp (-τ))/(1+Real.exp (-τ))*(ξ.im/(1-ξ.re))) := by
  let q := Real.exp (-τ)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hqr : ξ.re*q < 1 := by
    rcases le_total 0 ξ.re with hr' | hr'
    · have h := mul_le_mul_of_nonneg_left hq1 hr'
      linarith
    · have h := mul_nonpos_of_nonpos_of_nonneg hr' hq
      linarith
  have he : Complex.exp (-(τ:ℂ)) = (q:ℂ) := by
    dsimp [q]
    rw [Complex.ofReal_exp,Complex.ofReal_neg]
  have hf : 0 < (1-ξ*(q:ℂ)).re := by simp; nlinarith
  have hg : 0 < (1-ξ).re := by simp; linarith
  unfold argumentShift logShift
  rw [Complex.sub_im,Complex.log_im,Complex.log_im,he,
    arg_right_half_plane _ hf,arg_right_half_plane _ hg]
  simpa only [Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,add_zero,zero_add,sub_zero,zero_sub,neg_mul] using
    arctan_difference ξ.re ξ.im q hu hr hi hq hq1

theorem root_argumentShift (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hi : 0 ≤ ξ.im) (τ : ℝ) (hτ : 0 ≤ τ) :
    argumentShift ξ τ = Real.arctan
      ((1-Real.exp (-τ))/(1+Real.exp (-τ))*(ξ.im/(1-ξ.re))) := by
  have hne : ξ ≠ 1 := hξ.ne_one (by norm_num)
  have hr := FifthRootCoordinates.real_upper ξ hξ.pow_eq_one hne
  exact argumentShift_arctan ξ (FifthRootCoordinates.coordinate_square ξ hξ.pow_eq_one)
    (by linarith) hi τ hτ

end
end Borwein.ArctangentPhase
