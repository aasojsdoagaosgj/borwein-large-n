import Borwein.MomentIntegralTable

set_option autoImplicit false

namespace Borwein.RoundedMomentArithmetic
noncomputable section
open MomentIntegralTable

def num (D l : ℕ) : ℕ :=
  l*D^6+4*l^2*D^5+10*l^3*D^4+20*l^4*D^3+10*l^5*D^2+4*l^6*D+l^7
def den (D u : ℕ) : ℕ := D^4+u*D^3+u^2*D^2+u^3*D+u^4
def weight (k i : ℕ) : ℕ := (i+1)^(k+1)-i^(k+1)
def total (k m : ℕ) (v : ℕ → ℕ) : ℕ :=
  ∑ i ∈ Finset.range m, v i*weight k i

theorem den_pos (D u : ℕ) (hD : 0 < D) : 0 < den D u := by
  unfold den
  positivity

theorem homogeneous_ratio (D l u : ℕ) (hD : 0 < D) :
    VarianceInterval.numerator ((l:ℝ)/D)/GroupedWeights.denominator ((u:ℝ)/D)^2 =
      ((D*num D l:ℕ):ℝ)/(den D u:ℝ)^2 := by
  have hD0 : (D:ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hn : (den D u:ℝ) ≠ 0 := by exact_mod_cast (den_pos D u hD).ne'
  unfold VarianceInterval.numerator GroupedWeights.denominator num den at *
  push_cast at *
  field_simp
  <;> ring

theorem checked_lower (D E l u v : ℕ) (hD : 0 < D) (hE : 0 < E)
    (h : v*(den D u)^2 ≤ E*D*num D l) :
    (v:ℝ)/E ≤ VarianceInterval.numerator ((l:ℝ)/D)/GroupedWeights.denominator ((u:ℝ)/D)^2 := by
  rw [homogeneous_ratio D l u hD]
  have hE' : (0:ℝ) < E := by exact_mod_cast hE
  have hd : (0:ℝ) < (den D u:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast den_pos D u hD)
  apply (div_le_div_iff₀ hE' hd).mpr
  exact_mod_cast (show v*(den D u)^2 ≤ (D*num D l)*E by nlinarith [h])

theorem checked_upper (D E l u v : ℕ) (hD : 0 < D) (hE : 0 < E)
    (h : E*D*num D l ≤ v*(den D u)^2) :
    VarianceInterval.numerator ((l:ℝ)/D)/GroupedWeights.denominator ((u:ℝ)/D)^2 ≤ (v:ℝ)/E := by
  rw [homogeneous_ratio D l u hD]
  have hE' : (0:ℝ) < E := by exact_mod_cast hE
  have hd : (0:ℝ) < (den D u:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast den_pos D u hD)
  apply (div_le_div_iff₀ hd hE').mpr
  exact_mod_cast (show (D*num D l)*E ≤ v*(den D u)^2 by nlinarith [h])

theorem weight_cast (k i : ℕ) : (weight k i:ℝ) = ((i:ℝ)+1)^(k+1)-(i:ℝ)^(k+1) := by
  unfold weight
  rw [Nat.cast_sub (pow_le_pow_left' (Nat.le_succ i) (k+1))]
  push_cast
  rfl

theorem certificate_integer_sum (k m E : ℕ) (v : ℕ → ℕ) :
    certificate k m (fun i => (v i:ℝ)/E) =
      (total k m v:ℝ)/((E:ℝ)*((k:ℝ)+1)*(m:ℝ)^(k+1)) := by
  unfold certificate total
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [grid_powerMass,weight_cast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end Borwein.RoundedMomentArithmetic
