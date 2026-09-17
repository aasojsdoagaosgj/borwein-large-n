import Borwein.FifthRootSeparation
import Borwein.SincBounds

namespace Borwein.LargeBoxSeparation
noncomputable section
open Complex Set FifthRootSeparation

theorem cos_lower_six (x : ℝ) (hx : 0 ≤ x) :
    1-x^2/2+x^4/24-x^6/720 ≤ Real.cos x := by
  let f (t : ℝ) := Real.cos t-(1-t^2/2+t^4/24-t^6/720)
  have hd (t : ℝ) : deriv f t = -Real.sin t+t-t^3/6+t^5/120 := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    linarith [SincBounds.sin_le_quintic t (interior_subset ht)]
  have hb := hm (by simp) hx hx
  dsimp [f] at hb
  simp only [Real.cos_zero] at hb
  linarith

theorem sin_lower_seven (x : ℝ) (hx : 0 ≤ x) :
    x-x^3/6+x^5/120-x^7/5040 ≤ Real.sin x := by
  let f (t : ℝ) := Real.sin t-(t-t^3/6+t^5/120-t^7/5040)
  have hd (t : ℝ) : deriv f t = Real.cos t-(1-t^2/2+t^4/24-t^6/720) := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    linarith [cos_lower_six t (interior_subset ht)]
  have hb := hm (by simp) hx hx
  dsimp [f] at hb
  simp only [Real.sin_zero] at hb
  linarith

theorem cos_upper_eight (x : ℝ) (hx : 0 ≤ x) :
    Real.cos x ≤ 1-x^2/2+x^4/24-x^6/720+x^8/40320 := by
  let f (t : ℝ) := 1-t^2/2+t^4/24-t^6/720+t^8/40320-Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t-(t-t^3/6+t^5/120-t^7/5040) := by
    simp (disch := fun_prop) [f]
    ring
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    linarith [sin_lower_seven t (interior_subset ht)]
  have hb := hm (by simp) hx hx
  dsimp [f] at hb
  simp only [Real.cos_zero] at hb
  linarith

theorem endpoint_trig : (36/100:ℝ) ≤ Real.cos (6/5) ∧ Real.cos (6/5) ≤ 3624/10000 ∧
    Real.sin (6/5) ≤ 9321/10000 := by
  have hl := cos_lower_six (6/5) (by norm_num)
  have hu := cos_upper_eight (6/5) (by norm_num)
  have hs := (abs_le.mp (SineCertificate.polynomial_error (6/5) (by norm_num))).2
  norm_num [SineCertificate.polynomial,Finset.sum_range_succ,Nat.factorial] at hl hu hs
  constructor
  · linarith
  constructor <;> linarith

theorem cosine_lower (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 6/5) : (36/100:ℝ) ≤ Real.cos v := by
  apply endpoint_trig.1.trans
  exact Real.cos_le_cos_of_nonneg_of_le_pi hv0 (by linarith [Real.pi_gt_three]) hv1

def envelope (v : ℝ) : ℝ := (3091/10000:ℝ)*Real.cos v+(9511/10000:ℝ)*Real.sin v

theorem envelope_upper (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 6/5) : envelope v ≤ 9987/10000 := by
  have hm : MonotoneOn envelope (Icc (0:ℝ) (6/5)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (by unfold envelope; fun_prop) (by unfold envelope; fun_prop)
    intro t ht
    have ht' := interior_subset ht
    have hc := cosine_lower t ht'.1 ht'.2
    have hs := Real.sin_le_one t
    have hd : deriv envelope t = -(3091/10000:ℝ)*Real.sin t+(9511/10000:ℝ)*Real.cos t := by
      unfold envelope
      simp (disch := fun_prop)
    rw [hd]
    nlinarith
  have he := hm ⟨hv0,hv1⟩ (by norm_num) hv1
  unfold envelope at he ⊢
  have hc := endpoint_trig.2.1
  have hs := endpoint_trig.2.2
  linarith

theorem rotated_real_upper (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) (v : ℝ) (hv : |v| ≤ 6/5) :
    (rotated ξ v).re ≤ 9987/10000 := by
  have hc := cosine_lower |v| (abs_nonneg v) hv
  rw [Real.cos_abs] at hc
  have hr := FifthRootCoordinates.real_upper ξ hξ hne
  have hs := FifthRootCoordinates.imaginary_upper ξ hξ hne
  have hm := mul_le_mul_of_nonneg_right hr (by linarith : 0 ≤ Real.cos v)
  have hneg : -(ξ.im*Real.sin v) ≤ |ξ.im| * |Real.sin v| := by simpa only [abs_mul] using neg_le_abs (ξ.im*Real.sin v)
  have ha := mul_le_mul_of_nonneg_right hs (abs_nonneg (Real.sin v))
  have he := envelope_upper |v| (abs_nonneg v) hv
  have habs : |Real.sin v| = Real.sin |v| := Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [Real.pi_gt_three])
  unfold envelope at he
  rw [Real.cos_abs] at he
  rw [habs] at hneg ha
  have hb : ξ.re*Real.cos v-ξ.im*Real.sin v ≤ 9987/10000 := by linarith
  simpa [rotated,Complex.mul_re] using hb

theorem radial_distance (u : ℂ) (hu : ‖u‖ = 1) (hr : u.re ≤ 9987/10000) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (1/20:ℝ) ≤ ‖1-(ρ:ℂ)*u‖ := by
  have hs : u.re^2+u.im^2 = 1 := by
    have he := Complex.sq_norm u
    rw [hu] at he
    simpa [Complex.normSq_apply,pow_two] using he.symm
  have hm := congrArg (fun t : ℝ => ρ^2*t) hs
  have hn := Complex.sq_norm (1-(ρ:ℂ)*u)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_sub,add_zero] at hn
  have hp := mul_nonneg hρ (sub_nonneg.mpr hr)
  nlinarith [sq_nonneg (ρ-9987/10000),norm_nonneg (1-(ρ:ℂ)*u)]

theorem factor_gap (ξ z : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) (hz : |z.im| ≤ 6/5)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : (1/20:ℝ) ≤ ‖LogFactorDerivatives.kernel ξ z x‖ := by
  have hv : |-z.im*x| ≤ 6/5 := by
    rw [abs_mul,abs_neg,abs_of_nonneg hx.1]
    simpa using mul_le_mul hz hx.2 hx.1 (by norm_num : (0:ℝ) ≤ 6/5)
  unfold LogFactorDerivatives.kernel
  rw [FifthRootSeparation.factor_polar]
  exact radial_distance _ (rotated_norm ξ hξ _) (rotated_real_upper ξ hξ hne _ hv) _ (Real.exp_pos _).le

theorem coefficient_gap (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hz : |z.im| ≤ 6/5)
    (j : Fin 4) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    (1/20:ℝ) ≤ ‖LogFactorDerivatives.kernel (FiveRootProductExpansion.coefficients ξ j) z x‖ := by
  apply factor_gap _ z _ _ hz x hx
  · unfold FiveRootProductExpansion.coefficients
    rw [← pow_mul,mul_comm (j.val+1) 5,pow_mul,hξ.pow_eq_one,one_pow]
  · exact hξ.pow_ne_one_of_pos_of_lt (by omega) (by have h := j.isLt; omega)

end
end Borwein.LargeBoxSeparation
