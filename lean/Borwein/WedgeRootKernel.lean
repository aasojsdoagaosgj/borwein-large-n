import Borwein.LargeBoxSeparation

set_option autoImplicit false

namespace Borwein.WedgeRootKernel
noncomputable section
open Complex Set FifthRootSeparation

theorem endpoint_trig : Real.cos (3/4:ℝ) ≤ 183/250 ∧ Real.sin (3/4:ℝ) ≤ 6817/10000 := by
  have hc := LargeBoxSeparation.cos_upper_eight (3/4) (by norm_num)
  have hs := (abs_le.mp (SineCertificate.polynomial_error (3/4) (by norm_num))).2
  norm_num [SineCertificate.polynomial, Finset.sum_range_succ, Nat.factorial] at hc hs
  constructor <;> linarith

theorem envelope_upper (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 3/4) :
    LargeBoxSeparation.envelope v ≤ 7/8 := by
  have hm : MonotoneOn LargeBoxSeparation.envelope (Icc (0:ℝ) (3/4)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (by unfold LargeBoxSeparation.envelope; fun_prop) (by unfold LargeBoxSeparation.envelope; fun_prop)
    intro t ht
    have ht' := interior_subset ht
    have hc := LargeBoxSeparation.cosine_lower t ht'.1 (by linarith [ht'.2])
    have hs := Real.sin_le_one t
    have hd : deriv LargeBoxSeparation.envelope t =
        -(3091/10000:ℝ)*Real.sin t+(9511/10000:ℝ)*Real.cos t := by
      unfold LargeBoxSeparation.envelope
      simp (disch := fun_prop)
    rw [hd]
    linarith
  have he := hm ⟨hv0,hv1⟩ (by norm_num) hv1
  unfold LargeBoxSeparation.envelope at he ⊢
  have hc := endpoint_trig.1
  have hs := endpoint_trig.2
  linarith

theorem rotated_real_upper (ξ : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1) (v : ℝ) (hv : |v| ≤ 3/4) :
    (rotated ξ v).re ≤ 7/8 := by
  have hc := LargeBoxSeparation.cosine_lower |v| (abs_nonneg v) (by linarith)
  rw [Real.cos_abs] at hc
  have hr := FifthRootCoordinates.real_upper ξ hξ hne
  have hs := FifthRootCoordinates.imaginary_upper ξ hξ hne
  have hm := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ Real.cos v)
  have hneg : -(ξ.im*Real.sin v) ≤ |ξ.im| * |Real.sin v| := by
    simpa only [abs_mul] using neg_le_abs (ξ.im*Real.sin v)
  have ha := mul_le_mul_of_nonneg_right hs (abs_nonneg (Real.sin v))
  have he := envelope_upper |v| (abs_nonneg v) hv
  have habs := Real.abs_sin_eq_sin_abs_of_abs_le_pi (x := v) (by linarith [Real.pi_gt_three])
  unfold LargeBoxSeparation.envelope at he
  rw [Real.cos_abs] at he
  rw [habs] at hneg ha
  have hb : ξ.re*Real.cos v-ξ.im*Real.sin v ≤ 7/8 := by linarith
  simpa [rotated, Complex.mul_re] using hb

theorem radial_square_small (u : ℂ) (hu : ‖u‖=1) (hr : u.re ≤ 7/8) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ ≤ 4*‖1-(ρ:ℂ)*u‖^2 := by
  have hs : u.re^2+u.im^2=1 := by
    have he := Complex.sq_norm u
    rw [hu] at he
    simpa [Complex.normSq_apply, pow_two] using he.symm
  have hm := congrArg (fun t : ℝ => ρ^2*t) hs
  have hn := Complex.sq_norm (1-(ρ:ℂ)*u)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    zero_sub, add_zero] at hn
  have hp := mul_nonneg hρ (sub_nonneg.mpr hr)
  nlinarith [sq_nonneg (ρ-1)]

theorem radial_square_large (u : ℂ) (hu : ‖u‖=1) (ρ : ℝ) (hρ : 0 ≤ ρ) (hr : ρ ≤ 1/2) :
    ρ ≤ 4*‖1-(ρ:ℂ)*u‖^2 := by
  have ht := norm_sub_norm_le (1:ℂ) ((ρ:ℂ)*u)
  rw [norm_one, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ] at ht
  nlinarith [sq_nonneg (‖1-(ρ:ℂ)*u‖-1/2)]

theorem kernel_derivative_bound (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖ξ*exp (-z)/(1-ξ*exp (-z))^2‖ ≤ 4 := by
  let ρ : ℝ := Real.exp (-z.re)
  let u : ℂ := rotated ξ (-z.im)
  have hρ : 0 < ρ := Real.exp_pos _
  have hu : ‖u‖=1 := rotated_norm ξ hξ _
  have he : ξ*exp (-z) = (ρ:ℂ)*u := by
    simpa [LogFactorDerivatives.w, ρ, u] using factor_polar ξ z 1
  have hb : ρ ≤ 4*‖1-(ρ:ℂ)*u‖^2 := by
    by_cases hs : z.re ≤ 1
    · apply radial_square_small u hu _ ρ hρ.le
      apply rotated_real_upper ξ hξ hne
      rw [abs_neg]
      linarith
    · have hex : (2:ℝ) ≤ Real.exp z.re := by linarith [Real.add_one_le_exp z.re]
      have hr : ρ ≤ 1/2 := by
        dsimp [ρ]
        rw [Real.exp_neg]
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hex
      exact radial_square_large u hu ρ hρ.le hr
  have hd : 0 < ‖1-(ρ:ℂ)*u‖^2 := by nlinarith
  rw [he, norm_div, norm_pow, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  exact (div_le_iff₀ hd).mpr hb

def pole (ξ z : ℂ) : ℂ := ξ*exp (-z)/(1-ξ*exp (-z))

theorem denominator_ne_zero (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) : 1-ξ*exp (-z) ≠ 0 := by
  by_cases hr : z.re=0
  · have him : z.im=0 := by rw [hr] at hi; simpa using hi
    have he : z=0 := Complex.ext hr him
    simpa [he] using sub_ne_zero.mpr hne.symm
  · have hp : 0 < z.re := lt_of_le_of_ne hz (Ne.symm hr)
    have hn : ‖ξ*exp (-z)‖ < 1 := by
      rw [norm_mul, FiveRootProductExpansion.root_norm ξ hξ, one_mul, Complex.norm_exp, Complex.neg_re]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    intro he
    have hEq : ξ*exp (-z)=1 := (sub_eq_zero.mp he).symm
    rw [hEq, norm_one] at hn
    exact (lt_irrefl _ hn)

theorem pole_hasDerivAt (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) :
    HasDerivAt (pole ξ) (-ξ*exp (-z)/(1-ξ*exp (-z))^2) z := by
  have hu : HasDerivAt (fun t : ℂ => ξ*exp (-t)) (-ξ*exp (-z)) z := by
    exact ((((hasDerivAt_id z).neg).cexp).const_mul ξ).congr_deriv (by simp)
  have hd := denominator_ne_zero ξ z hξ hne hz hi
  have he := hu.div (hu.const_sub 1) hd
  exact he.congr_deriv (by ring)

theorem deriv_pole_bound (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 ≤ z.re) (hi : |z.im| ≤ 3*z.re/4) : ‖deriv (pole ξ) z‖ ≤ 4 := by
  rw [(pole_hasDerivAt ξ z hξ hne hz hi).deriv]
  simpa only [neg_mul, neg_div, norm_neg] using kernel_derivative_bound ξ z hξ hne hz hi

end
end Borwein.WedgeRootKernel
