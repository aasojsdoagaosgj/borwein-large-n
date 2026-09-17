import Borwein.EndpointCuspTransfer

set_option autoImplicit false

namespace Borwein.EndpointEtaTwo
noncomputable section
open Complex EndpointEta EndpointEtaMobius EndpointCuspTransfer
open scoped Real

theorem sqrt_components_positive (z : ℂ) (hz : 0 < z.im) :
    0 < (sqrt z).re ∧ 0 < (sqrt z).im := by
  have hn := Complex.abs_re_lt_norm.mpr hz.ne'
  have hr : 0 < ‖z‖+z.re := by linarith [neg_abs_le z.re]
  have hi : 0 < ‖z‖-z.re := by linarith [le_abs_self z.re]
  constructor
  · rw [sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_pos.mpr (div_pos hr (by norm_num))
  · rw [sqrt, Complex.cpow_inv_two_im_eq_sqrt hz.le]
    exact Real.sqrt_pos.mpr (div_pos hi (by norm_num))

theorem sqrt_mul_upper (x y : ℂ) (hx : 0 < x.im) (hy : 0 < y.im)
    (hxy : 0 < (x*y).im) : sqrt (x*y) = sqrt x*sqrt y := by
  have hs : sqrt (x*y)^2 = (sqrt x*sqrt y)^2 := by simp [mul_pow, sqrt]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with he | he
  · exact he
  · have hp := sqrt_components_positive (x*y) hxy
    have hx' := sqrt_components_positive x hx
    have hy' := sqrt_components_positive y hy
    have hm : 0 < (sqrt x*sqrt y).im := by
      rw [Complex.mul_im]
      exact add_pos (mul_pos hx'.1 hy'.2) (mul_pos hx'.2 hy'.1)
    have hh := congrArg Complex.im he
    rw [Complex.neg_im] at hh
    linarith

/-- The matrix (2,1;5,3) as lower(2) * translate(1) * lower(1). -/
theorem eta_matrix_two (z : ℂ) (hz : 0 < z.im) :
    ModularForm.eta ((2*z+1)/(5*z+3)) =
      exp (-(Real.pi:ℂ)*I/6)*sqrt (5*z+3)*ModularForm.eta z := by
  have hz1 : z+1 ≠ 0 := by intro h; have hh := congrArg Complex.im h; simp at hh; linarith
  have hz5 : 5*z+3 ≠ 0 := by intro h; have hh := congrArg Complex.im h; simp at hh; linarith
  let t : ℂ := z/(z+1)
  have ht : 0 < t.im := by
    have he : t.im = z.im/Complex.normSq (z+1) := by
      dsimp [t]
      simp [Complex.div_im]
      ring
    rw [he]
    exact div_pos hz (Complex.normSq_pos.mpr hz1)
  have hv : 0 < (t+1).im := by simpa using ht
  have hp : (2*(t+1)+1)*(z+1) = 5*z+3 := by dsimp [t]; field_simp; ring
  have hd : 2*(t+1)+1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hp
    exact hz5 hp.symm
  have ha : (t+1)/(2*(t+1)+1) = (2*z+1)/(5*z+3) := by
    apply (div_eq_div_iff hd hz5).mpr
    rw [← hp]
    dsimp [t]
    field_simp
    ring
  have hs : sqrt (2*(t+1)+1)*sqrt (z+1) = sqrt (5*z+3) := by
    rw [← sqrt_mul_upper]
    · rw [hp]
    · simpa using mul_pos (by norm_num : (0:ℝ)<2) ht
    · simpa using hz
    · rw [hp]; simpa using mul_pos (by norm_num : (0:ℝ)<5) hz
  have h1 : ModularForm.eta t = exp (-(Real.pi:ℂ)*I/12)*sqrt (z+1)*ModularForm.eta z := by
    simpa [t] using eta_lower z 1 hz
  have h2 := eta_lower (t+1) 2 hv
  norm_num only [Nat.cast_ofNat] at h2
  rw [ha, eta_add_one, h1] at h2
  rw [h2]
  calc
    _ = (exp (-(Real.pi:ℂ)*I*2/12)*exp ((Real.pi:ℂ)*I/12)*exp (-(Real.pi:ℂ)*I/12))*
        (sqrt (2*(t+1)+1)*sqrt (z+1))*ModularForm.eta z := by ring
    _ = _ := by rw [hs, ← Complex.exp_add, ← Complex.exp_add]; congr 2; ring

theorem eta_cusp_two (s : ℂ) (hs : 0 < s.im) :
    ModularForm.eta ((s+2)/5) = exp ((Real.pi:ℂ)*I*(-1/6))*sqrt (-1/s)*
      ModularForm.eta ((-1/s-3)/5) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  let u : ℂ := (-1/s-3)/5
  have hu : 0 < u.im := by
    have hi := inverse_upper s hs
    simpa [u] using div_pos hi (by norm_num : (0:ℝ)<5)
  have hd : 5*u+3 = -1/s := by dsimp [u]; ring
  have ha : (2*u+1)/(5*u+3) = (s+2)/5 := by rw [hd]; dsimp [u]; field_simp; ring
  have he := eta_matrix_two u hu
  rw [ha, hd] at he
  convert he using 1 <;> congr 2 <;> ring

theorem G_cusp_two (s : ℂ) (hs : 0 < s.im) :
    G (q ((s+2)/5)) = exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-3)/5))/euler (q (-1/s))) := by
  have he := G_from_eta s 2 3 (-1/6) hs (by simpa using eta_cusp_two s hs)
  norm_num at he
  simpa only [one_div] using he

end
end Borwein.EndpointEtaTwo
