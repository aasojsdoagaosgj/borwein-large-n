import Borwein.FiveDivisibleResidues

namespace Borwein.FiveDivisibleVariation
noncomputable section
open scoped BigOperators
open FiveDivisibleResidues (distance)
open ShiftedResidues (phase)
open ShiftedPoleBudget (actualPhase variation phase_error)
open ResidueBlockCount (blocks)

def nonresonant (B K : ℕ) := (Finset.Icc 1 K).filter (fun k => ¬ B ∣ k)

theorem phase_distance_lower (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (B : ℕ) (hden : q.den = 5*B) (k : ℕ) (j : Fin 4) :
    ((distance q B k j:ℝ)-k/Q)/(q.den:ℝ) ≤
      |actualPhase ξ k j-round (actualPhase ξ k j)| := by
  have hb : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hr := round_le (phase q k j) (round (actualPhase ξ k j))
  have ht := abs_add_le (phase q k j-actualPhase ξ k j)
    (actualPhase ξ k j-round (actualPhase ξ k j))
  rw [sub_add_sub_cancel] at ht
  have he := phase_error ξ Q q h k j
  have hid : ((distance q B k j:ℝ)-k/Q)/(q.den:ℝ) =
      |phase q k j-round (phase q k j)|-k/((q.den:ℝ)*Q) := by
    rw [FiveDivisibleResidues.distance_eq q B k hden j]
    field_simp
  rw [hid]
  linarith

theorem local_variation (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (B : ℕ) (hden : q.den = 5*B) (k : ℕ) (j : Fin 4)
    (hr : (k:ℝ)/Q < distance q B k j) :
    variation ξ q k j ≤ Real.pi*q.den*k /
      (8*Q*(distance q B k j:ℝ)*((distance q B k j:ℝ)-k/Q)) := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hr0 : (0:ℝ) < distance q B k j :=
    lt_of_le_of_lt (by positivity) hr
  have hp : 0 < (distance q B k j:ℝ)-k/Q := sub_pos.mpr hr
  have hn : (distance q B k j:ℝ)/(q.den:ℝ) ≤ |phase q k j-round (phase q k j)| := by
    rw [FiveDivisibleResidues.distance_eq q B k hden j]
    exact le_of_eq (mul_div_cancel_left₀ _ (by positivity))
  have hs := PoleVariation.pole_bound_of_distances (phase q k j) (actualPhase ξ k j)
    ((distance q B k j:ℝ)/(q.den:ℝ)) (((distance q B k j:ℝ)-k/Q)/(q.den:ℝ))
    (by positivity) (by positivity) hn (phase_distance_lower ξ Q hQ q h B hden k j)
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (phase_error ξ Q q h k j) Real.pi_pos.le)
    (show 0 ≤ 8*((distance q B k j:ℝ)/(q.den:ℝ))*
      (((distance q B k j:ℝ)-k/Q)/(q.den:ℝ)) by positivity)
  refine hs.trans (hm.trans_eq ?_)
  field_simp


theorem weighted_term (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B)
    (hKQ : K < Q) (k : ℕ) (hk : k ∈ nonresonant B K) (j : Fin 4) :
    ZeroPoleBudget.weight η k*variation ξ q k j ≤
      (Real.pi*q.den/(8*Q))/((1-(K:ℝ)/Q)*(distance q B k j:ℝ)^2) := by
  have hkfilter := Finset.mem_filter.mp hk
  have hk' := Finset.mem_Icc.mp hkfilter.1
  have hkp : 0 < k := by omega
  have hr : (1:ℝ) ≤ distance q B k j := by
    exact_mod_cast FiveDivisibleResidues.distance_positive q B k hb hkfilter.2 j
  have hx : (k:ℝ)/Q < 1 := (div_lt_one (Nat.cast_pos.mpr hQ)).mpr
    (by exact_mod_cast (show k < Q by omega))
  have h := mul_le_mul_of_nonneg_left (local_variation ξ Q hQ q hq B hb k j (hx.trans_le hr))
    (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity)
  have hh := PoleVariation.weighted_denominator_bound
    (Real.pi*q.den/(8*Q)) (distance q B k j) k K Q (ZeroPoleBudget.weight η k)
    (by positivity) hr (by positivity) (by exact_mod_cast hk'.2)
    (by exact_mod_cast hKQ) (PoleVariation.fourier_weight_cancellation η hη k hkp)
  have he : ZeroPoleBudget.weight η k*(Real.pi*q.den*k /
      (8*Q*(distance q B k j:ℝ)*((distance q B k j:ℝ)-k/Q))) =
      ZeroPoleBudget.weight η k*((Real.pi*q.den/(8*Q))*k/
        ((distance q B k j:ℝ)*((distance q B k j:ℝ)-k/Q))) := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at h
  exact h.trans hh

theorem weighted_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B)
    (hKQ : K < Q) :
    (∑ k ∈ nonresonant B K, ∑ j : Fin 4, ZeroPoleBudget.weight η k*variation ξ q k j) ≤
      (2*blocks K B:ℕ)*(Real.pi^3*q.den/(48*Q*(1-(K:ℝ)/Q))) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have h := Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => weighted_term ξ η hη Q K hQ q hq B hb hKQ k hk j))
  have he : (∑ k ∈ nonresonant B K, ∑ j : Fin 4,
      (Real.pi*q.den/(8*Q))/((1-(K:ℝ)/Q)*(distance q B k j:ℝ)^2)) =
      (Real.pi*q.den/(8*Q*(1-(K:ℝ)/Q)))*
        ∑ k ∈ nonresonant B K, ∑ j : Fin 4, (1:ℝ)/(distance q B k j:ℝ)^2 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at h
  have hsub : (∑ k ∈ nonresonant B K, ∑ j : Fin 4, (1:ℝ)/(distance q B k j:ℝ)^2) ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, (1:ℝ)/(distance q B k j:ℝ)^2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro k _ _
    exact Finset.sum_nonneg (fun j _ => by positivity)
  have hh := mul_le_mul_of_nonneg_left
    (hsub.trans (FiveDivisibleResidues.inverse_square_sum q B hb K))
    (show 0 ≤ Real.pi*q.den/(8*Q*(1-(K:ℝ)/Q)) by positivity)
  refine h.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem five_frequency_distance (q : ℚ) (B k : ℕ) (hb : q.den = 5*B)
    (hk : ¬ B ∣ k) (m : ℤ) :
    1/(B:ℝ) ≤ |5*(k:ℝ)*q-m| := by
  have hn : (k:ℤ)*q.num-m*B ≠ 0 := by
    intro he
    have hd : (B:ℤ) ∣ (k:ℤ)*q.num := by
      rw [sub_eq_zero.mp he]
      exact dvd_mul_left _ _
    have hdk := (FiveDivisibleResidues.period_coprime q B hb).dvd_of_dvd_mul_right hd
    exact hk (by exact_mod_cast hdk)
  have hnum : (1:ℝ) ≤ |(k:ℝ)*q.num-m*B| := by exact_mod_cast Int.one_le_abs hn
  have hB : (0:ℝ) < B := Nat.cast_pos.mpr (FiveDivisibleResidues.period_pos q B hb)
  have hb' : (q.den:ℝ) = 5*B := by exact_mod_cast hb
  have hid : 5*(k:ℝ)*q-m = ((k:ℝ)*q.num-m*B)/B := by
    rw [Rat.cast_def,hb']
    field_simp
  rw [hid,abs_div,abs_of_pos hB]
  exact div_le_div_of_nonneg_right hnum hB.le

theorem five_frequency_avoids_integers (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B k : ℕ) (hb : q.den = 5*B)
    (hk : ¬ B ∣ k) (hkQ : k < Q) (m : ℤ) : 5*(k:ℝ)*ξ ≠ m := by
  intro hm
  have hdist := five_frequency_distance q B k hb hk m
  have herr := DirichletCover.scaled_error ξ Q q hq (5*k)
  have hb' : (q.den:ℝ) = 5*B := by exact_mod_cast hb
  have hB : (0:ℝ) < B := Nat.cast_pos.mpr (FiveDivisibleResidues.period_pos q B hb)
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have he : ((5*k:ℕ):ℝ)/((q.den:ℝ)*Q) = (k:ℝ)/((B:ℝ)*Q) := by
    push_cast
    rw [hb']
    field_simp
  rw [he] at herr
  have he' : ((5*k:ℕ):ℝ)*q-((5*k:ℕ):ℝ)*ξ = 5*(k:ℝ)*q-m := by
    push_cast
    rw [hm]
  rw [abs_sub_comm,he'] at herr
  have hlt : (k:ℝ)/((B:ℝ)*Q) < 1/B := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < (B:ℝ)*Q)).mpr
    have heq : (1/(B:ℝ))*(B*Q) = Q := by field_simp
    rw [heq]
    exact_mod_cast hkQ
  exact (hdist.trans herr).not_gt hlt

theorem five_sine_ne_zero (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (B k : ℕ) (hb : q.den = 5*B)
    (hk : ¬ B ∣ k) (hkQ : k < Q) : Real.sin (Real.pi*(5*(k:ℝ)*ξ)) ≠ 0 := by
  intro hs
  obtain ⟨m,hm⟩ := Real.sin_eq_zero_iff.mp hs
  apply five_frequency_avoids_integers ξ Q hQ q hq B k hb hk hkQ m
  apply mul_left_cancel₀ Real.pi_ne_zero
  nlinarith

end
end Borwein.FiveDivisibleVariation
