import Borwein.ShiftedPoleBudget

namespace Borwein.LargeDenominatorVariation
noncomputable section
open scoped BigOperators

theorem sine_frequency_ne_zero (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (k : ℕ)
    (hk : ¬ q.den ∣ k) (hkQ : k < Q) : Real.sin (Real.pi*((k:ℝ)*ξ)) ≠ 0 := by
  intro hs
  obtain ⟨m,hm⟩ := Real.sin_eq_zero_iff.mp hs
  apply DirichletCover.nonresonant_avoids_integers ξ Q hQ q hq k hk hkQ m
  apply mul_left_cancel₀ Real.pi_ne_zero
  nlinarith

theorem profile_term (ξ : ℝ) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) (hK : 2*K < q.den) (k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
    |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))| ≤
      (8/5:ℝ)*ZeroPoleBudget.variation ξ q k+
      (2/5:ℝ)*∑ j : Fin 4, ShiftedPoleBudget.variation ξ q k j := by
  have hk' := Finset.mem_Icc.mp hk
  have hkn : ¬ q.den ∣ k := by
    intro hd
    have hh := Nat.le_of_dvd (by omega : 0 < k) hd
    omega
  have h5kn : ¬ q.den ∣ 5*k := fun h => hkn (hb5.dvd_mul_left.mp h)
  have h5kQ : 5*k < Q := by omega
  have hnom : DirichletCover.Near (q:ℝ) Q q := ⟨hq.1, by simp; positivity⟩
  have h1 := sine_frequency_ne_zero (q:ℝ) Q hQ q hnom (5*k) h5kn h5kQ
  have h2 := sine_frequency_ne_zero ξ Q hQ q hq (5*k) h5kn h5kQ
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
    (hKQ : 5*K < Q) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, ZeroPoleBudget.weight η k*
      |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))|) ≤
      Real.pi^3*q.den/(30*Q)*(1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q)) := by
  have ht := Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (profile_term ξ Q K hQ q hq hb5 hKQ hK k hk)
    (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity))
  have he : (∑ k ∈ Finset.Icc 1 K, ZeroPoleBudget.weight η k*
      ((8/5:ℝ)*ZeroPoleBudget.variation ξ q k+
        (2/5:ℝ)*∑ j : Fin 4, ShiftedPoleBudget.variation ξ q k j)) =
      (8/5:ℝ)*(∑ k ∈ Finset.Icc 1 K, ZeroPoleBudget.weight η k*ZeroPoleBudget.variation ξ q k)+
      (2/5:ℝ)*(∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4,
        ZeroPoleBudget.weight η k*ShiftedPoleBudget.variation ξ q k j) := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl
    · intro k _; ring
    · intro k _; apply Finset.sum_congr rfl; intro j _; ring
  rw [he] at ht
  have hh := add_le_add (ZeroPoleBudget.profile_zero_pole_budget ξ η hη Q K hQ q hq hK)
    (ShiftedPoleBudget.profile_shifted_budget ξ η hη Q K hQ q hq hb5 hKQ hK)
  refine ht.trans (hh.trans_eq ?_)
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem nominal_transfer (ξ η : ℝ) (hη : 0 ≤ η) (Q K : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5)
    (hKQ : 5*K < Q) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, ZeroPoleBudget.weight η k*
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))) ≤
      (∑ k ∈ Finset.Icc 1 K, ZeroPoleBudget.weight η k*
        RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q)))+
      Real.pi^3*q.den/(30*Q)*(1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q)) := by
  have ht : ∀ k : ℕ,
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ)) ≤
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))+
        |RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
          RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ))| := by
    intro k
    linarith [neg_le_abs (RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q))-
      RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*ξ)))]
  have h := Finset.sum_le_sum (s := Finset.Icc 1 K) (fun k _ =>
    mul_le_mul_of_nonneg_left (ht k)
      (show 0 ≤ ZeroPoleBudget.weight η k by unfold ZeroPoleBudget.weight; positivity))
  simp only [mul_add,Finset.sum_add_distrib] at h
  exact h.trans (add_le_add le_rfl (profile_sum ξ η hη Q K hQ q hq hb5 hKQ hK))

end
end Borwein.LargeDenominatorVariation
