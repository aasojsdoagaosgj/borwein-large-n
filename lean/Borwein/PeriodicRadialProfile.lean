import Borwein.PeriodicProductWeights

set_option autoImplicit false

namespace Borwein.PeriodicRadialProfile
noncomputable section
open Complex PeriodicEulerProduct PeriodicLossSeries PeriodicProductWeights

def ray (v θ : ℝ) : ℂ := exp (-(v:ℂ)+(θ:ℂ)*I)
def gProduct (q : ℂ) : ℂ := residueProduct (0:Fin 4) q*residueProduct (3:Fin 4) q
def hProduct (q : ℂ) : ℂ := residueProduct (1:Fin 4) q*residueProduct (2:Fin 4) q

theorem product_identities (p : Fin 3) (q : ℂ) : product (weights p) q =
    ![gProduct q^2, gProduct q*hProduct q, hProduct q^2] p := by
  have hf : Fin.succ (2:Fin 3)=(3:Fin 4) := by decide
  fin_cases p <;> norm_num [product, weights, gProduct, hProduct, Fin.prod_univ_succ, hf] <;> ring

theorem ray_norm (v θ : ℝ) : ‖ray v θ‖=Real.exp (-v) := by simp [ray, Complex.norm_exp]

theorem ray_power (v θ : ℝ) (k : ℕ) :
    ray v θ^k = exp (-((k:ℝ)*v:ℂ)+((k:ℝ)*θ:ℂ)*I) := by
  rw [ray, ← exp_nat_mul]
  congr 1
  push_cast
  ring

theorem radialMass_upper (p : Fin 3) (v : ℝ) (hv : 0 ≤ v) : radialMass p v ≤ 4 := by
  have he : (∑ j : Fin 4, (weights p j:ℝ))=4 := by exact_mod_cast weight_sum p
  rw [radialMass, ← he]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_of_le_one_right (Nat.cast_nonneg _)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hv

theorem radial_quotient_lower (p : Fin 3) (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/2000) :
    (4-10*v)/(5*v) ≤ radialMass p v/(1-Real.exp (-5*v)) := by
  have hd : 0 < 1-Real.exp (-5*v) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he : 1-Real.exp (-5*v) ≤ 5*v := by linarith [Real.add_one_le_exp (-5*v)]
  exact div_le_div₀ (radialMass_nonneg p v) (radialMass_lower p v) hd he

theorem loss_formula (p : Fin 3) (v θ : ℝ) :
    totalLoss (weights p) (ray v θ) = radialMass p v/(1-Real.exp (-5*v))-
      (numerator (weights p) (ray v θ)/(1-exp (-(5*v:ℝ)+((5*θ:ℝ):ℂ)*I))).re := by
  rw [totalLoss_quotient, ray_norm, radial_numerator, ray_power]
  have he : (Real.exp (-v):ℂ)^5=(Real.exp (-5*v):ℂ) := by
    rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
    congr 2
    ring
  rw [he]
  have hr : ((radialMass p v:ℂ)/(1-(Real.exp (-5*v):ℂ))).re = radialMass p v/(1-Real.exp (-5*v)) := by
    rw [show (1:ℂ)-(Real.exp (-5*v):ℂ)=((1-Real.exp (-5*v):ℝ):ℂ) by push_cast; rfl,
      Complex.div_ofReal_re, Complex.ofReal_re]
  rw [hr]
  norm_num

theorem decay_formula (p : Fin 3) (v θ : ℝ) (hv : 0 < v) :
    ‖product (weights p) (ray v θ)‖ ≤ ‖product (weights p) (Real.exp (-v):ℂ)‖*
      Real.exp (-(radialMass p v/(1-Real.exp (-5*v))-
        (numerator (weights p) (ray v θ)/(1-exp (-(5*v:ℝ)+((5*θ:ℝ):ℂ)*I))).re)) := by
  have hq : ‖ray v θ‖ < 1 := by rw [ray_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := product_decay (weights p) (ray v θ) hq
  simpa only [ray_norm, loss_formula] using h

end
end Borwein.PeriodicRadialProfile
