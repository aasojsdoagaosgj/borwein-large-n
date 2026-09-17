import Borwein.EndpointCuspConjugation
import Borwein.EndpointEtaBounds
import Borwein.FivePoleCircle

set_option autoImplicit false

namespace Borwein.EndpointRootAsymptotic
noncomputable section
open Complex EndpointEta EndpointCuspTransfer EndpointEtaTwo EndpointCuspConjugation
open scoped Real

def dual (j : Fin 4) : ℕ := ![1,3,2,4] j
def kappa (j : Fin 4) : ℂ := ![exp (-(Real.pi:ℂ)*I/5),1,1,exp ((Real.pi:ℂ)*I/5)] j
def sPoint (w : ℂ) : ℂ := 5*I*w/(2*Real.pi)
def main (w : ℂ) : ℂ := exp ((2*(Real.pi:ℂ)^2/75)/w-w/6)
def correction (j : Fin 4) (w : ℂ) : ℂ :=
  euler (q (-(dual j:ℂ)/5)*exp (-4*(Real.pi:ℂ)^2/(25*w)))/
    euler (exp (-4*(Real.pi:ℂ)^2/(5*w)))

theorem cusp_table (j : Fin 4) (s : ℂ) (hs : 0 < s.im) :
    G (q ((s+(j.val+1:ℕ))/5)) = kappa j*exp ((Real.pi:ℂ)*I*(s+1/s)/15)*
      (euler (q ((-1/s-dual j)/5))/euler (q (-1/s))) := by
  fin_cases j
  · simpa [dual, kappa] using G_cusp_one s hs
  · simpa [dual, kappa] using G_cusp_two s hs
  · simpa [dual, kappa] using G_cusp_three s hs
  · simpa [dual, kappa] using G_cusp_four s hs

theorem sPoint_upper (w : ℂ) (hw : 0 < w.re) : 0 < (sPoint w).im := by
  unfold sPoint
  rw [show (2:ℂ)*Real.pi = ((2*Real.pi:ℝ):ℂ) by push_cast; rfl]
  rw [Complex.div_ofReal_im]
  simpa using div_pos (mul_pos (by norm_num : (0:ℝ)<5) hw)
    (mul_pos (by norm_num : (0:ℝ)<2) Real.pi_pos)

theorem q_root (l : ℕ) : q ((l:ℂ)/5) = FivePoleCircle.zeta^l := by
  rw [FivePoleCircle.zeta, AngularKernel.circle_eq_exp, ← Complex.exp_nat_mul]
  unfold q
  congr 1
  push_cast
  ring

theorem root_coordinate (w : ℂ) (l : ℕ) :
    q ((sPoint w+l)/5) = FivePoleCircle.zeta^l*exp (-w) := by
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← q_root]
  unfold q sPoint
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring_nf
  simp [I_sq] <;> ring

theorem dual_coordinate (w : ℂ) (d : ℕ) (hw : 0 < w.re) :
    q ((-1/sPoint w-d)/5) = q (-(d:ℂ)/5)*exp (-4*(Real.pi:ℂ)^2/(25*w)) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold q sPoint
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring_nf

theorem denominator_coordinate (w : ℂ) (hw : 0 < w.re) :
    q (-1/sPoint w) = exp (-4*(Real.pi:ℂ)^2/(5*w)) := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold q sPoint
  congr 1
  field_simp
  ring_nf

theorem main_coordinate (w : ℂ) (hw : 0 < w.re) :
    exp ((Real.pi:ℂ)*I*(sPoint w+1/sPoint w)/15) = main w := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold sPoint main
  congr 1
  field_simp
  ring_nf
  simp [I_sq]

/-- Manuscript (5.3)--(5.4), including all four exact multipliers. -/
theorem four_root_expansion (j : Fin 4) (w : ℂ) (hw : 0 < w.re) :
    G (FivePoleCircle.zeta^(j.val+1)*exp (-w)) = kappa j*main w*correction j w := by
  have he := cusp_table j (sPoint w) (sPoint_upper w hw)
  rw [root_coordinate, main_coordinate w hw, dual_coordinate w (dual j) hw,
    denominator_coordinate w hw] at he
  exact he

theorem root_unit_norm (d : ℕ) : ‖q (-(d:ℂ)/5)‖ = 1 := by
  simp [q, Complex.norm_exp, map_ofNat]

/-- The same error budget as the positive cusp applies to every primitive cusp correction. -/
theorem correction_error (j : Fin 4) (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hy : |y| ≤ 3*v/4) : ‖correction j ((v:ℂ)+(y:ℂ)*I)-1‖ ≤ 10*Real.exp (-1/v) := by
  unfold correction
  apply EndpointEtaBounds.quotient_error_small _ _ _ (EndpointEtaBounds.small_exponential v hv hV)
  · rw [norm_mul, root_unit_norm, one_mul]
    exact EndpointEtaBounds.primitive_transformed_norm v y hv hy
  · have hc : (25/16:ℝ) ≤ 4*Real.pi^2/5 := by nlinarith [Real.pi_gt_d2]
    have he : -4*(Real.pi:ℂ)^2/(5*((v:ℂ)+(y:ℂ)*I)) =
        -((4*Real.pi^2/5:ℝ):ℂ)/((v:ℂ)+(y:ℂ)*I) := by
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    exact EndpointEtaBounds.transformed_norm (4*Real.pi^2/5) v y hv hy hc

theorem dual_is_inverse (j : Fin 4) : ((j.val+1)*dual j)%5 = 1 := by
  fin_cases j <;> norm_num [dual]

theorem q_inverse_root (d : ℕ) : q (-(d:ℂ)/5) = FivePoleCircle.zeta^(-(d:ℤ)) := by
  rw [zpow_neg, zpow_natCast, ← q_root]
  unfold q
  rw [← Complex.exp_neg]
  congr 1
  ring

theorem kappa_ne_zero (j : Fin 4) : kappa j ≠ 0 := by
  fin_cases j <;> simp [kappa, Complex.exp_ne_zero]

theorem normalized_four_root (j : Fin 4) (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hy : |y| ≤ 3*v/4) :
    ‖G (FivePoleCircle.zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))/
        (kappa j*main ((v:ℂ)+(y:ℂ)*I))-1‖ ≤ 10*Real.exp (-1/v) := by
  have hw : 0 < ((v:ℂ)+(y:ℂ)*I).re := by simpa using hv
  have hm : kappa j*main ((v:ℂ)+(y:ℂ)*I) ≠ 0 :=
    mul_ne_zero (kappa_ne_zero j) (Complex.exp_ne_zero _)
  rw [four_root_expansion j _ hw, mul_div_cancel_left₀ _ hm]
  exact correction_error j v y hv hV hy

end
end Borwein.EndpointRootAsymptotic
