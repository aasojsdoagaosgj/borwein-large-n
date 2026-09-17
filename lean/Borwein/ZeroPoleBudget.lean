import Borwein.ResidueMultiplicity

namespace Borwein.ZeroPoleBudget
noncomputable section
open scoped BigOperators

def weight (η : ℝ) (k : ℕ) := Real.exp (-η*k)/(k:ℝ)
def variation (ξ : ℝ) (q : ℚ) (k : ℕ) :=
  ‖PoleVariation.pole (2*Real.pi*((k:ℝ)*q))-
    PoleVariation.pole (2*Real.pi*((k:ℝ)*ξ))‖

theorem weighted_term (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hK : 2*K < q.den)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
    weight η k*variation ξ q k ≤
      (Real.pi*q.den/(8*Q))/((1-(K:ℝ)/Q)*(DirichletCover.residue q k)^2) := by
  have hk' := Finset.mem_Icc.mp hk
  have hden := hq.1
  have hkpos : 0 < k := by omega
  have hKQ : K < Q := by omega
  have hkQ : k < Q := by omega
  have hkn : ¬ q.den ∣ k := by
    intro hd
    have hh := Nat.le_of_dvd hkpos hd
    omega
  have hp := PoleVariation.near_pole_variation_nonresonant ξ Q hQ q hq k hkn hkQ
  have hw : 0 ≤ weight η k := by unfold weight; positivity
  have hm := mul_le_mul_of_nonneg_left hp hw
  have hid : Real.pi*q.den*k /
      (8*Q*DirichletCover.residue q k*(DirichletCover.residue q k-(k:ℝ)/Q)) =
      (Real.pi*q.den/(8*Q))*k /
        (DirichletCover.residue q k*(DirichletCover.residue q k-(k:ℝ)/Q)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hid] at hm
  exact hm.trans (PoleVariation.weighted_denominator_bound _ _ _ _ _ _
    (by positivity) (DirichletCover.residue_ge_one q k hkn) (Nat.cast_nonneg k)
    (by exact_mod_cast hk'.2) (by exact_mod_cast hKQ)
    (PoleVariation.fourier_weight_cancellation η hη k hkpos))

theorem weighted_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, weight η k*variation ξ q k) ≤
      Real.pi^3*q.den/(48*Q*(1-(K:ℝ)/Q)) := by
  have hden := hq.1
  have hKQ : (K:ℝ) < Q := by exact_mod_cast (show K < Q by omega)
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr hKQ)
  have h := Finset.sum_le_sum (fun k hk => weighted_term ξ η hη Q K hQ q hq hK k hk)
  have he : (∑ k ∈ Finset.Icc 1 K,
      (Real.pi*q.den/(8*Q))/((1-(K:ℝ)/Q)*(DirichletCover.residue q k)^2)) =
      (Real.pi*q.den/(8*Q*(1-(K:ℝ)/Q)))*
        ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(DirichletCover.residue q k)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left (ResidueMultiplicity.residue_inverse_square_sum q K hK)
    (show 0 ≤ Real.pi*q.den/(8*Q*(1-(K:ℝ)/Q)) by positivity)
  refine h.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem profile_zero_pole_budget (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hK : 2*K < q.den) :
    (8/5:ℝ)*(∑ k ∈ Finset.Icc 1 K, weight η k*variation ξ q k) ≤
      Real.pi^3*q.den/(30*Q*(1-(K:ℝ)/Q)) := by
  have h := mul_le_mul_of_nonneg_left (weighted_sum ξ η hη Q K hQ q hq hK)
    (by norm_num : (0:ℝ) ≤ 8/5)
  refine h.trans_eq ?_
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end Borwein.ZeroPoleBudget
