import Borwein.FiniteBlockDenominators

namespace Borwein.RadialCorrectionEnvelope
noncomputable section
open scoped BigOperators
open FiniteBlockDenominators (correction radialCost nominalCost attenuation)
open ZeroPoleBudget (weight)

def margin (q : ℚ) (Q k : ℕ) : ℝ := DirichletCover.residue q k-(k:ℝ)/Q

def envelope (q : ℚ) (Q k N : ℕ) (A T : ℝ) : ℝ :=
  (1+Real.exp (-(k:ℝ)*A))*Real.sinh (2*((k:ℝ)*T/(5*N)))*(q.den:ℝ)^2/
    (8*margin q Q k*margin q Q (5*k))

def cost (s : Finset ℕ) (q : ℚ) (Q N : ℕ) (A T η : ℝ) : ℝ :=
  ∑ k ∈ s, weight η k*envelope q Q k N A T

theorem sine_product_lower (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q) (q : ℚ)
    (hq : DirichletCover.Near ξ Q q) (k : ℕ)
    (h1 : 0 < margin q Q k) (h5 : 0 < margin q Q (5*k)) :
    8*margin q Q k*margin q Q (5*k)/(q.den:ℝ)^2 ≤
      2*|Real.sin ((k:ℝ)*(2*Real.pi*ξ)/2)| *
        |Real.sin (5*((k:ℝ)*(2*Real.pi*ξ))/2)| := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hs1 := AngularKernel.residue_sine_lower ξ Q hQ q hq k
  have hs5 := AngularKernel.residue_sine_lower ξ Q hQ q hq (5*k)
  change 2*margin q Q k/q.den ≤ _ at hs1
  change 2*margin q Q (5*k)/q.den ≤ _ at hs5
  rw [show Real.pi*((k:ℝ)*ξ) = (k:ℝ)*(2*Real.pi*ξ)/2 by ring] at hs1
  rw [show Real.pi*(((5*k:ℕ):ℝ)*ξ) = 5*((k:ℝ)*(2*Real.pi*ξ))/2 by push_cast; ring] at hs5
  have hm := mul_le_mul hs1 hs5 (by positivity) (abs_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 2)
  rw [← mul_assoc (2:ℝ) |Real.sin ((k:ℝ)*(2*Real.pi*ξ)/2)|
    |Real.sin (5*((k:ℝ)*(2*Real.pi*ξ))/2)|] at hh
  refine le_trans (le_of_eq ?_) hh
  field_simp
  norm_num

theorem correction_residue_upper (n k : ℕ) (τ ξ : ℝ) (hτ : 0 ≤ τ)
    (Q : ℕ) (hQ : 0 < Q) (q : ℚ) (hq : DirichletCover.Near ξ Q q)
    (h1 : 0 < margin q Q k) (h5 : 0 < margin q Q (5*k)) :
    correction n k τ (2*Real.pi*ξ) ≤ envelope q Q k n τ τ := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hd := sine_product_lower ξ Q hQ q hq k h1 h5
  have hp : 0 < 8*margin q Q k*margin q Q (5*k)/(q.den:ℝ)^2 := by positivity
  have hn : 0 ≤ (1+Real.exp (-(k:ℝ)*τ))*Real.sinh (2*((k:ℝ)*τ/(5*n))) := by positivity
  have h := div_le_div_of_nonneg_left hn hp hd
  unfold correction envelope
  refine h.trans_eq ?_
  field_simp

theorem argument_le (n N k : ℕ) (hN : 0 < N) (hn : N ≤ n) (τ T : ℝ)
    (hτ : 0 ≤ τ) (hT : τ ≤ T) : (k:ℝ)*τ/(5*n) ≤ (k:ℝ)*T/(5*N) := by
  have hNp : (0:ℝ) < 5*N := by positivity
  have hdn : (5:ℝ)*N ≤ 5*n := by exact_mod_cast (show 5*N ≤ 5*n by omega)
  have hT0 : 0 ≤ T := hτ.trans hT
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg k))
    (by positivity : (0:ℝ) ≤ 5*n)).trans
      (div_le_div_of_nonneg_left (by positivity) hNp hdn)

theorem envelope_mono (q : ℚ) (Q k n N : ℕ) (hN : 0 < N) (hn : N ≤ n)
    (A τ T : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T)
    (h1 : 0 < margin q Q k) (h5 : 0 < margin q Q (5*k)) :
    envelope q Q k n τ τ ≤ envelope q Q k N A T := by
  have he : Real.exp (-(k:ℝ)*τ) ≤ Real.exp (-(k:ℝ)*A) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hA (neg_nonpos.mpr (Nat.cast_nonneg k)))
  have hs := Real.sinh_le_sinh.mpr
    (mul_le_mul_of_nonneg_left (argument_le n N k hN hn τ T hτ hT) (by norm_num : (0:ℝ) ≤ 2))
  have hm := mul_le_mul (add_le_add le_rfl he) hs
    (by positivity : 0 ≤ Real.sinh (2*((k:ℝ)*τ/(5*n))))
    (by positivity : 0 ≤ 1+Real.exp (-(k:ℝ)*A))
  unfold envelope
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hm (sq_nonneg _)) (by positivity)

theorem interval_upper (n N k : ℕ) (hN : 0 < N) (hn : N ≤ n) (A τ T ξ : ℝ)
    (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (hq : DirichletCover.Near ξ Q q)
    (h1 : 0 < margin q Q k) (h5 : 0 < margin q Q (5*k)) :
    correction n k τ (2*Real.pi*ξ) ≤ envelope q Q k N A T := by
  exact (correction_residue_upper n k τ ξ hτ Q hQ q hq h1 h5).trans
    (envelope_mono q Q k n N hN hn A τ T hτ hA hT h1 h5)

theorem margin_positive (q : ℚ) (Q k : ℕ) (hQ : 0 < Q) (hkQ : k < Q)
    (hk : ¬ q.den ∣ k) : 0 < margin q Q k := by
  have h := (div_lt_one (Nat.cast_pos.mpr hQ : (0:ℝ) < Q)).mpr
    (by exact_mod_cast hkQ : (k:ℝ) < Q)
  exact sub_pos.mpr (h.trans_le (DirichletCover.residue_ge_one q k hk))

theorem coprime_margins (q : ℚ) (hb5 : q.den.Coprime 5) (Q K : ℕ) (hQ : 0 < Q)
    (hKQ : 5*K < Q) (k : ℕ) (hk : k ∈ GeneralDenominatorVariation.nonresonant q K) :
    0 < margin q Q k ∧ 0 < margin q Q (5*k) := by
  have hkf := Finset.mem_filter.mp hk
  have hk' := Finset.mem_Icc.mp hkf.1
  exact ⟨margin_positive q Q k hQ (by omega) hkf.2,
    margin_positive q Q (5*k) hQ (by omega) (fun h => hkf.2 (hb5.dvd_mul_left.mp h))⟩

theorem five_residue_ge (q : ℚ) (B k : ℕ) (hb : q.den = 5*B) (hk : ¬ B ∣ k) :
    5 ≤ DirichletCover.residue q (5*k) := by
  have h := FiveDivisibleVariation.five_frequency_distance q B k hb hk
    (round (((5*k:ℕ):ℝ)*q))
  have hm := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q.den : (0:ℝ) ≤ q.den)
  have hB : (B:ℝ) ≠ 0 := by exact_mod_cast (FiveDivisibleResidues.period_pos q B hb).ne'
  have he : (q.den:ℝ)*(1/(B:ℝ)) = 5 := by
    rw [hb]
    push_cast
    field_simp
  rw [he] at hm
  simpa only [DirichletCover.residue,Nat.cast_mul,Nat.cast_ofNat] using hm

theorem divisible_margins (q : ℚ) (B : ℕ) (hb : q.den = 5*B)
    (Q K : ℕ) (hQ : 0 < Q) (hKQ : K < Q) (k : ℕ)
    (hk : k ∈ FiveDivisibleVariation.nonresonant B K) :
    0 < margin q Q k ∧ 0 < margin q Q (5*k) := by
  have hkf := Finset.mem_filter.mp hk
  have hk' := Finset.mem_Icc.mp hkf.1
  have hbkn : ¬ q.den ∣ k := fun hd => hkf.2
    (dvd_trans (show B ∣ q.den by rw [hb]; exact dvd_mul_left _ _) hd)
  refine ⟨margin_positive q Q k hQ (by omega) hbkn, ?_⟩
  have hfrac : ((5*k:ℕ):ℝ)/Q < 5 := by
    apply (div_lt_iff₀ (Nat.cast_pos.mpr hQ)).mpr
    exact_mod_cast (show 5*k < 5*Q by omega)
  exact sub_pos.mpr (hfrac.trans_le (five_residue_ge q B k hb hkf.2))

theorem cost_upper (s : Finset ℕ) (n N : ℕ) (hN : 0 < N) (hn : N ≤ n)
    (A τ T ξ η : ℝ) (hτ : 0 ≤ τ) (hA : A ≤ τ) (hT : τ ≤ T)
    (Q : ℕ) (hQ : 0 < Q) (q : ℚ) (hq : DirichletCover.Near ξ Q q)
    (hm : ∀ k ∈ s, 0 < margin q Q k ∧ 0 < margin q Q (5*k)) :
    radialCost s n τ (2*Real.pi*ξ) η ≤ cost s q Q N A T η := by
  exact Finset.sum_le_sum (fun k hk => mul_le_mul_of_nonneg_left
    (interval_upper n N k hN hn A τ T ξ hτ hA hT Q hQ q hq (hm k hk).1 (hm k hk).2)
    (show 0 ≤ weight η k by unfold weight; positivity))

theorem nominal_cost_mono (s : Finset ℕ) (q : ℚ) (A τ η : ℝ) (hA : A ≤ τ) :
    nominalCost s q τ η ≤ nominalCost s q A η := by
  apply Finset.sum_le_sum
  intro k _
  have he : attenuation τ k ≤ attenuation A k := by
    unfold attenuation
    exact div_le_div_of_nonneg_right (add_le_add le_rfl
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hA (neg_nonpos.mpr (Nat.cast_nonneg k))))) (by norm_num)
  have hprofile : 0 ≤ RadialKernelProfile.profile (2*Real.pi*((k:ℝ)*q)) := by
    unfold RadialKernelProfile.profile
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left he (by unfold weight; positivity)) hprofile

end
end Borwein.RadialCorrectionEnvelope
