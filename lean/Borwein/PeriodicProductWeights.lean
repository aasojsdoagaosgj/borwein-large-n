import Borwein.PeriodicLossSeries
import Borwein.FifthRootCoordinates
import Borwein.EndpointTailGlobalLog

set_option autoImplicit false

namespace Borwein.PeriodicProductWeights
noncomputable section
open Complex PeriodicLossSeries

def weights (p : Fin 3) : Fin 4 → ℕ := ![![2,0,0,2], ![1,1,1,1], ![0,2,2,0]] p
def radialMass (p : Fin 3) (v : ℝ) : ℝ :=
  ∑ j : Fin 4, (weights p j:ℝ)*Real.exp (-((j.val+1:ℕ):ℝ)*v)
def rootValue (p : Fin 3) (t : ℝ) : ℝ := ![4*t, -1, -2-4*t] p

theorem weight_sum (p : Fin 3) : ∑ j : Fin 4, weights p j=4 := by
  fin_cases p <;> norm_num [weights, Fin.sum_univ_succ]

theorem first_moment (p : Fin 3) : ∑ j : Fin 4, weights p j*(j.val+1)=10 := by
  fin_cases p <;> norm_num [weights, Fin.sum_univ_succ]

theorem real_lower (ξ : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1) : -(8091/10000:ℝ) ≤ ξ.re := by
  have h := FifthRootCoordinates.real_quadratic ξ hξ hne
  by_contra hh
  have ht := lt_of_not_ge hh
  nlinarith [sq_nonneg (ξ.re+8091/10000)]

theorem conjugate_pair (ξ : ℂ) (hξ : ξ^5=1) : ξ+ξ^4=((2*ξ.re:ℝ):ℂ) := by
  have hn := FiveRootProductExpansion.root_norm ξ hξ
  have hi : ξ⁻¹=ξ^4 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using hξ
  rw [← hi, Complex.inv_eq_conj hn, Complex.add_conj]

theorem root_numerator (p : Fin 3) (ξ : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1) :
    numerator (weights p) ξ=(rootValue p ξ.re:ℂ) := by
  have hp := conjugate_pair ξ hξ
  have hc : ξ^4+ξ^3+ξ^2+ξ+1=0 := by
    have he : (ξ^4+ξ^3+ξ^2+ξ+1)*(ξ-1)=ξ^5-1 := by ring
    rw [hξ, sub_self] at he
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hne)
  fin_cases p
  · norm_num [numerator, weights, rootValue, Fin.sum_univ_succ]
    push_cast at hp
    linear_combination 2*hp
  · norm_num [numerator, weights, rootValue, Fin.sum_univ_succ]
    linear_combination hc
  · norm_num [numerator, weights, rootValue, Fin.sum_univ_succ]
    push_cast at hp
    linear_combination 2*hc-2*hp

theorem nontrivial_root_bound (p : Fin 3) (ξ : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1) :
    (numerator (weights p) ξ).im=0 ∧ (numerator (weights p) ξ).re ≤ 5/4 := by
  rw [root_numerator p ξ hξ hne]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  have hu := FifthRootCoordinates.real_upper ξ hξ hne
  have hl := real_lower ξ hξ hne
  fin_cases p <;> norm_num [rootValue] <;> linarith

theorem radialMass_nonneg (p : Fin 3) (v : ℝ) : 0 ≤ radialMass p v := by
  unfold radialMass
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)

theorem radialMass_lower (p : Fin 3) (v : ℝ) : 4-10*v ≤ radialMass p v := by
  have hs : (∑ j : Fin 4, (weights p j:ℝ))=4 := by exact_mod_cast weight_sum p
  have hm : (∑ j : Fin 4, (weights p j:ℝ)*((j.val+1:ℕ):ℝ))=10 := by exact_mod_cast first_moment p
  have he : 4-10*v = ∑ j : Fin 4, (weights p j:ℝ)*(1-((j.val+1:ℕ):ℝ)*v) := by
    rw [← hs, ← hm, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  linarith [Real.add_one_le_exp (-((j.val+1:ℕ):ℝ)*v)]

theorem numerator_norm (p : Fin 3) (q : ℂ) (v : ℝ) (hq : ‖q‖=Real.exp (-v)) :
    ‖numerator (weights p) q‖ ≤ radialMass p v := by
  unfold numerator radialMass
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, Complex.norm_natCast, norm_pow, EndpointTailGlobalLog.radius_power q v hq (j.val+1)]

theorem radial_numerator (p : Fin 3) (v : ℝ) :
    numerator (weights p) (Real.exp (-v):ℂ)=(radialMass p v:ℂ) := by
  unfold numerator radialMass
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  have he : Real.exp (-v)^(j.val+1)=Real.exp (-((j.val+1:ℕ):ℝ)*v) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← Complex.ofReal_pow, he]
  push_cast
  rfl

end
end Borwein.PeriodicProductWeights
