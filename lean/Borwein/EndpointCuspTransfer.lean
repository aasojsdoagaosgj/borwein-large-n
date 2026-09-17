import Borwein.EndpointEtaMobius

set_option autoImplicit false

namespace Borwein.EndpointCuspTransfer
noncomputable section
open Complex EndpointEta EndpointEtaMobius
open scoped Real

theorem J_ne_zero (s : ℂ) (hs : 0 < s.im) : J s ≠ 0 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [J, sqrt_eq_exp (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hs0)]
  exact Complex.exp_ne_zero _

theorem sqrt_inverse_mul_J (s : ℂ) (hs : 0 < s.im) : sqrt (-1/s)*J s = sqrt I := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hv := inverse_upper s hs
  have hp : J (-1/s)*J s = 1 := by
    have hrv : 0 < (-I*(-1/s)).re := by simpa using hv
    have hrs : 0 < (-I*s).re := by simpa using hs
    rw [J, J, ← sqrt_mul_right _ _ hrv hrs]
    have he : (-I*(-1/s))*(-I*s) = 1 := by field_simp; simp [← mul_assoc]
    rw [he, Complex.sqrt_one]
  rw [sqrt_upper _ hv, mul_assoc, hp, mul_one]

theorem sqrt_I_exp : sqrt I = exp ((Real.pi:ℂ)*I/4) := by
  rw [sqrt_eq_exp I_ne_zero, Complex.log_I]
  congr 1
  ring

/-- Transfer an eta cusp multiplier to the original Euler-product ratio. -/
theorem G_from_eta (s : ℂ) (l d : ℕ) (a : ℝ) (hs : 0 < s.im)
    (hN : ModularForm.eta ((s+l)/5) = exp ((Real.pi:ℂ)*I*a)*sqrt (-1/s)*
      ModularForm.eta ((-1/s-d)/5)) :
    G (q ((s+l)/5)) = exp ((Real.pi:ℂ)*I*(a+1/4-((l:ℂ)+d)/60))*
      exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-d)/5))/euler (q (-1/s))) := by
  have hD : ModularForm.eta (5*((s+l)/5)) =
      exp ((Real.pi:ℂ)*I*l/12)*ModularForm.eta s := by
    rw [show (5:ℂ)*((s+l)/5)=s+l by ring]
    exact eta_add_nat s l
  have hV := eta_S s hs
  have hJ := sqrt_inverse_mul_J s hs
  have hJ0 := J_ne_zero s hs
  have hE0 := ModularForm.eta_ne_zero hs
  have hr : ModularForm.eta ((s+l)/5)/ModularForm.eta (5*((s+l)/5)) =
      exp ((Real.pi:ℂ)*I*(a-(l:ℂ)/12))*sqrt I*
      (ModularForm.eta ((-1/s-d)/5)/ModularForm.eta (-1/s)) := by
    have hex : exp ((Real.pi:ℂ)*I*(a-(l:ℂ)/12)) =
        exp ((Real.pi:ℂ)*I*a)/exp ((Real.pi:ℂ)*I*l/12) := by
      rw [← Complex.exp_sub]
      congr 1
      ring
    rw [hN, hD, hex, ← hJ, hV]
    field_simp
  rw [G_eta, hr, eta_product, eta_product, mul_div_mul_comm, ← Complex.exp_sub, sqrt_I_exp]
  simp only [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem eta_cusp_one (s : ℂ) (hs : 0 < s.im) :
    ModularForm.eta ((s+1)/5) = exp ((Real.pi:ℂ)*I*(-5/12))*sqrt (-1/s)*
      ModularForm.eta ((-1/s-1)/5) := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  let u : ℂ := (-1/s-1)/5
  have hu : 0 < u.im := by
    have hi := inverse_upper s hs
    simpa [u] using div_pos hi (by norm_num : (0:ℝ)<5)
  have hd : (5:ℂ)*u+1 = -1/s := by dsimp [u]; ring
  have ha : u/((5:ℂ)*u+1) = (s+1)/5 := by
    rw [hd]
    dsimp [u]
    field_simp
    ring
  have he := eta_lower u 5 hu
  norm_num only [Nat.cast_ofNat] at he
  rw [ha, hd] at he
  convert he using 1 <;> congr 2 <;> ring

theorem G_cusp_one (s : ℂ) (hs : 0 < s.im) :
    G (q ((s+1)/5)) = exp (-(Real.pi:ℂ)*I/5)*
      exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-1)/5))/euler (q (-1/s))) := by
  have he := G_from_eta s 1 1 (-5/12) hs (by simpa using eta_cusp_one s hs)
  norm_num at he
  convert he using 1 <;> congr 2 <;> ring

end
end Borwein.EndpointCuspTransfer
