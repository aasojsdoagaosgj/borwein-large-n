import Borwein.ShiftedBlockCount

namespace Borwein.GeneralDenominatorVariation
noncomputable section
open scoped BigOperators
open ResidueBlockCount (blocks)

def nonresonant (q : ℚ) (K : ℕ) := (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ k)

theorem zero_weighted_term (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hKQ : K < Q)
    (k : ℕ) (hk : k ∈ nonresonant q K) :
    ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k ≤
      (Real.pi*q.den/(8*Q))/((1-(K:ℝ)/Q)*(DirichletCover.residue q k)^2) := by
  have hkfilter := Finset.mem_filter.mp hk
  have hk' := Finset.mem_Icc.mp hkfilter.1
  have hkpos : 0 < k := by omega
  have hkQ : k < Q := by omega
  have hkn : ¬ q.den ∣ k := hkfilter.2
  have hp := PoleVariation.near_pole_variation_nonresonant ξ Q hQ q hq k hkn hkQ
  have hw : 0 ≤ ZeroPoleBudget.weight η k := by unfold ZeroPoleBudget.weight; positivity
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


theorem zero_weighted_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hKQ : K < Q) :
    (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k) ≤
      (2*blocks K q.den:ℕ)*(Real.pi^3*q.den/(48*Q*(1-(K:ℝ)/Q))) := by
  have hKQ' : (K:ℝ) < Q := by exact_mod_cast hKQ
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr hKQ')
  have h := Finset.sum_le_sum (fun k hk => zero_weighted_term ξ η hη Q K hQ q hq hKQ k hk)
  have he : (∑ k ∈ nonresonant q K,
      (Real.pi*q.den/(8*Q))/((1-(K:ℝ)/Q)*(DirichletCover.residue q k)^2)) =
      (Real.pi*q.den/(8*Q*(1-(K:ℝ)/Q)))*
        ∑ k ∈ nonresonant q K, (1:ℝ)/(DirichletCover.residue q k)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left (ResidueBlockCount.nonresonant_inverse_square_sum q K)
    (show 0 ≤ Real.pi*q.den/(8*Q*(1-(K:ℝ)/Q)) by positivity)
  refine h.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


theorem shifted_weighted_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) :
    (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, ZeroPoleBudget.weight η k*ShiftedPoleBudget.variation ξ q k j) ≤
      (2*blocks K q.den:ℕ)*(Real.pi^3*q.den/(2*Q*(1-5*(K:ℝ)/Q))) := by
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hcut : 0 < 1-5*(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have h := Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => ShiftedPoleBudget.weighted_term ξ η hη Q K hQ q hq hb5 hKQ k hk j))
  have he : (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4,
      (25*Real.pi*q.den/(8*Q))/((1-5*(K:ℝ)/Q)*(ShiftedResidues.distance q k j:ℝ)^2)) =
      (25*Real.pi*q.den/(8*Q*(1-5*(K:ℝ)/Q)))*
        ∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, (1:ℝ)/(ShiftedResidues.distance q k j:ℝ)^2 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [he] at h
  have hh := mul_le_mul_of_nonneg_left (ShiftedBlockCount.inverse_square_sum q hb5 K)
    (show 0 ≤ 25*Real.pi*q.den/(8*Q*(1-5*(K:ℝ)/Q)) by positivity)
  refine h.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring


theorem profile_term (ξ : ℝ) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) (k : ℕ) (hk : k ∈ nonresonant q K) :
    |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))| ≤
      (8/5:ℝ)*ZeroPoleBudget.variation ξ q k+
      (2/5:ℝ)*∑ j : Fin 4, ShiftedPoleBudget.variation ξ q k j := by
  have hkfilter := Finset.mem_filter.mp hk
  have hk' := Finset.mem_Icc.mp hkfilter.1
  have hkn : ¬ q.den ∣ k := hkfilter.2
  have h5kn : ¬ q.den ∣ 5*k := fun h => hkn (hb5.dvd_mul_left.mp h)
  have h5kQ : 5*k < Q := by omega
  have hnom : DirichletCover.Near (q:ℝ) Q q := ⟨hq.1, by simp; positivity⟩
  have h1 := LargeDenominatorVariation.sine_frequency_ne_zero (q:ℝ) Q hQ q hnom (5*k) h5kn h5kQ
  have h2 := LargeDenominatorVariation.sine_frequency_ne_zero ξ Q hQ q hq (5*k) h5kn h5kQ
  have he (x : ℝ) : 5*(2*Real.pi*((k:ℝ)*x))/2 = Real.pi*((5*k:ℕ):ℝ)*x := by
    push_cast
    ring
  have hh := FivePoleCircle.profile_variation (2*Real.pi*((k:ℝ)*q))
    (2*Real.pi*((k:ℝ)*ξ)) (by rw [he]; simpa only [mul_assoc] using h1)
    (by rw [he]; simpa only [mul_assoc] using h2)
  have ha (x : ℝ) (j : Fin 4) :
      2*Real.pi*((k:ℝ)*x)+2*Real.pi*(j.val+1)/5 =
      2*Real.pi*((k:ℝ)*x+(j.val+1)/5) := by ring
  simp_rw [ha] at hh
  exact hh


theorem profile_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) :
    (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
      |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))|) ≤
      (2*blocks K q.den:ℕ)*(Real.pi^3*q.den/(30*Q)*
        (1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q))) := by
  have ht := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (profile_term ξ Q K hQ q hq hb5 hKQ k hk)
    (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity))
  have he : (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
      ((8/5:ℝ)*ZeroPoleBudget.variation ξ q k+
        (2/5:ℝ)*∑ j : Fin 4, ShiftedPoleBudget.variation ξ q k j)) =
      (8/5:ℝ)*(∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k)+
      (2/5:ℝ)*(∑ k ∈ nonresonant q K, ∑ j : Fin 4,
        ZeroPoleBudget.weight η k*ShiftedPoleBudget.variation ξ q k j) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl
    · intro k _; ring
    · intro k _; apply Finset.sum_congr rfl; intro j _; ring
  rw [he] at ht
  have hsub : (∑ k ∈ nonresonant q K, ∑ j : Fin 4,
      ZeroPoleBudget.weight η k*ShiftedPoleBudget.variation ξ q k j) ≤
      ∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4,
        ZeroPoleBudget.weight η k*ShiftedPoleBudget.variation ξ q k j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro k _ _
    apply Finset.sum_nonneg
    intro j _
    unfold ZeroPoleBudget.weight ShiftedPoleBudget.variation
    positivity
  have hh := add_le_add
    (mul_le_mul_of_nonneg_left (zero_weighted_sum ξ η hη Q K hQ q hq (by omega))
      (by norm_num : (0:ℝ) ≤ 8/5))
    (mul_le_mul_of_nonneg_left
      (hsub.trans (shifted_weighted_sum ξ η hη Q K hQ q hq hb5 hKQ))
      (by norm_num : (0:ℝ) ≤ 2/5))
  refine ht.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem nominal_transfer (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) :
    (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))) ≤
      (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q)))+
      (2*blocks K q.den:ℕ)*(Real.pi^3*q.den/(30*Q)*
        (1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q))) := by
  have ht : ∀ k : ℕ,
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ)) ≤
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))+
        |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
          RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))| := by
    intro k
    linarith [neg_le_abs (RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ)))]
  have h := Finset.sum_le_sum (s := nonresonant q K) (fun k _ =>
    mul_le_mul_of_nonneg_left (ht k)
      (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity))
  simp only [mul_add,Finset.sum_add_distrib] at h
  exact h.trans (add_le_add le_rfl (profile_sum ξ η hη Q K hQ q hq hb5 hKQ))

def multiplicity (q : ℚ) (K : ℕ) : ℕ :=
  if 2*K < q.den then 1 else 2*blocks K q.den

theorem nonresonant_eq_all (q : ℚ) (K : ℕ) (hK : 2*K < q.den) :
    nonresonant q K = Finset.Icc 1 K := by
  apply Finset.filter_eq_self.mpr
  intro k hk hd
  have hk' := Finset.mem_Icc.mp hk
  have hb := Nat.le_of_dvd (by omega : 0 < k) hd
  omega

theorem unified_profile_sum (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) :
    (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
      |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))|) ≤
      (multiplicity q K:ℝ)*(Real.pi^3*q.den/(30*Q)*
        (1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q))) := by
  by_cases hK : 2*K < q.den
  · simpa only [multiplicity,if_pos hK,Nat.cast_one,one_mul,nonresonant_eq_all q K hK]
      using LargeDenominatorVariation.profile_sum ξ η hη Q K hQ q hq hb5 hKQ hK
  · simpa only [multiplicity,if_neg hK]
      using profile_sum ξ η hη Q K hQ q hq hb5 hKQ

theorem unified_nominal_transfer (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) :
    (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))) ≤
      (∑ k ∈ nonresonant q K, ZeroPoleBudget.weight η k*
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q)))+
      (multiplicity q K:ℝ)*(Real.pi^3*q.den/(30*Q)*
        (1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q))) := by
  by_cases hK : 2*K < q.den
  · simpa only [multiplicity,if_pos hK,Nat.cast_one,one_mul,nonresonant_eq_all q K hK]
      using LargeDenominatorVariation.nominal_transfer ξ η hη Q K hQ q hq hb5 hKQ hK
  · simpa only [multiplicity,if_neg hK]
      using nominal_transfer ξ η hη Q K hQ q hq hb5 hKQ

end
end Borwein.GeneralDenominatorVariation
