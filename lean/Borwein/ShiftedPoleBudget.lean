import Borwein.NonFiveSquareSum

namespace Borwein.ShiftedPoleBudget
noncomputable section
open scoped BigOperators
open ShiftedResidues

def actualPhase (ξ : ℝ) (k : ℕ) (j : Fin 4) := (k:ℝ)*ξ+(j.val+1)/5
def variation (ξ : ℝ) (q : ℚ) (k : ℕ) (j : Fin 4) :=
  ‖PoleVariation.pole (2*Real.pi*phase q k j)-
    PoleVariation.pole (2*Real.pi*actualPhase ξ k j)‖

theorem phase_error (ξ : ℝ) (Q : ℕ) (q : ℚ) (h : DirichletCover.Near ξ Q q)
    (k : ℕ) (j : Fin 4) :
    |phase q k j-actualPhase ξ k j| ≤ k/((q.den:ℝ)*Q) := by
  have hh := DirichletCover.scaled_error ξ Q q h k
  simpa only [phase,actualPhase,add_sub_add_right_eq_sub,abs_sub_comm] using hh

theorem phase_distance_lower (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (k : ℕ) (j : Fin 4) :
    ((distance q k j:ℝ)-5*k/Q)/(5*q.den) ≤
      |actualPhase ξ k j-round (actualPhase ξ k j)| := by
  have hb : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr := round_le (phase q k j) (round (actualPhase ξ k j))
  have ht := abs_add_le (phase q k j-actualPhase ξ k j)
    (actualPhase ξ k j-round (actualPhase ξ k j))
  rw [sub_add_sub_cancel] at ht
  have he := phase_error ξ Q q h k j
  have hid : ((distance q k j:ℝ)-5*k/Q)/(5*q.den) =
      |phase q k j-round (phase q k j)|-k/((q.den:ℝ)*Q) := by
    rw [distance_eq]
    field_simp
  rw [hid]
  linarith

theorem local_variation (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (k : ℕ) (j : Fin 4)
    (hr : 5*(k:ℝ)/Q < distance q k j) :
    variation ξ q k j ≤ 25*Real.pi*q.den*k /
      (8*Q*(distance q k j:ℝ)*((distance q k j:ℝ)-5*k/Q)) := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hr0 : (0:ℝ) < distance q k j :=
    lt_of_le_of_lt (by positivity) hr
  have hp : 0 < (distance q k j:ℝ)-5*k/Q := sub_pos.mpr hr
  have hn : (distance q k j:ℝ)/(5*q.den) ≤ |phase q k j-round (phase q k j)| := by
    rw [distance_eq]
    exact le_of_eq (mul_div_cancel_left₀ _ (by positivity))
  have hs := PoleVariation.pole_bound_of_distances (phase q k j) (actualPhase ξ k j)
    ((distance q k j:ℝ)/(5*q.den)) (((distance q k j:ℝ)-5*k/Q)/(5*q.den))
    (by positivity) (by positivity) hn (phase_distance_lower ξ Q hQ q h k j)
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (phase_error ξ Q q h k j) Real.pi_pos.le)
    (show 0 ≤ 8*((distance q k j:ℝ)/(5*q.den))*
      (((distance q k j:ℝ)-5*k/Q)/(5*q.den)) by positivity)
  refine hs.trans (hm.trans_eq ?_)
  field_simp
  ring

theorem weighted_term (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) (k : ℕ) (hk : k ∈ Finset.Icc 1 K) (j : Fin 4) :
    ZeroPoleBudget.weight η k*variation ξ q k j ≤
      (25*Real.pi*q.den/(8*Q))/((1-5*(K:ℝ)/Q)*(distance q k j:ℝ)^2) := by
  have hk' := Finset.mem_Icc.mp hk
  have hkp : 0 < k := by omega
  have hr : (1:ℝ) ≤ distance q k j := by
    exact_mod_cast ShiftedResidues.distance_positive q hb5 k j
  have hx : 5*(k:ℝ)/Q < 1 := (div_lt_one (Nat.cast_pos.mpr hQ)).mpr
    (by exact_mod_cast (show 5*k < Q by omega))
  have h := mul_le_mul_of_nonneg_left (local_variation ξ Q hQ q hq k j (hx.trans_le hr))
    (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity)
  have hw : (ZeroPoleBudget.weight η k/5)*(5*(k:ℝ)) ≤ 1 := by
    have he : (ZeroPoleBudget.weight η k/5)*(5*(k:ℝ)) = ZeroPoleBudget.weight η k*k := by ring
    rw [he]
    exact PoleVariation.fourier_weight_cancellation η hη k hkp
  have hh := PoleVariation.weighted_denominator_bound
    (25*Real.pi*q.den/(8*Q)) (distance q k j) (5*k) (5*K) Q
    (ZeroPoleBudget.weight η k/5) (by positivity) hr (by positivity)
    (by exact_mod_cast (show 5*k ≤ 5*K by omega)) (by exact_mod_cast hKQ) hw
  have he : ZeroPoleBudget.weight η k*(25*Real.pi*q.den*k /
      (8*Q*(distance q k j:ℝ)*((distance q k j:ℝ)-5*k/Q))) =
      (ZeroPoleBudget.weight η k/5)*((25*Real.pi*q.den/(8*Q))*(5*k)/
        ((distance q k j:ℝ)*((distance q k j:ℝ)-5*k/Q))) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at h
  exact h.trans hh

theorem weighted_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, ZeroPoleBudget.weight η k*variation ξ q k j) ≤
      Real.pi^3*q.den/(2*Q*(1-5*(K:ℝ)/Q)) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcut : 0 < 1-5*(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have h := Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => weighted_term ξ η hη Q K hQ q hq hb5 hKQ k hk j))
  have he : (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4,
      (25*Real.pi*q.den/(8*Q))/((1-5*(K:ℝ)/Q)*(distance q k j:ℝ)^2)) =
      (25*Real.pi*q.den/(8*Q*(1-5*(K:ℝ)/Q)))*
        ∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, (1:ℝ)/(distance q k j:ℝ)^2 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left (NonFiveSquareSum.shifted_inverse_square_sum q hb5 K hK)
    (show 0 ≤ 25*Real.pi*q.den/(8*Q*(1-5*(K:ℝ)/Q)) by positivity)
  refine h.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem profile_shifted_budget (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) (hK : 2*K < q.den) :
    (2/5:ℝ)*(∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4,
      ZeroPoleBudget.weight η k*variation ξ q k j) ≤
      Real.pi^3*q.den/(5*Q*(1-5*(K:ℝ)/Q)) := by
  have h := mul_le_mul_of_nonneg_left (weighted_sum ξ η hη Q K hQ q hq hb5 hKQ hK)
    (by norm_num : (0:ℝ) ≤ 2/5)
  refine h.trans_eq ?_
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end
end Borwein.ShiftedPoleBudget
