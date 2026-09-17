import Borwein.FiniteBlockLocalization

namespace Borwein.FiniteBlockDenominators
noncomputable section
open scoped BigOperators
open FiniteBlockLocalization (point blockBound tail)
open ZeroPoleBudget (weight)
open RadialKernelProfile (profile)

def attenuation (τ : ℝ) (k : ℕ) := (1+Real.exp (-(k:ℝ)*τ))/2

def correction (n k : ℕ) (τ θ : ℝ) :=
  (1+Real.exp (-(k:ℝ)*τ))*Real.sinh (2*((k:ℝ)*τ/(5*n)))/
    (2*|Real.sin ((k:ℝ)*θ/2)| * |Real.sin (5*((k:ℝ)*θ)/2)|)

def nominalCost (s : Finset ℕ) (q : ℚ) (τ η : ℝ) :=
  ∑ k ∈ s, weight η k*attenuation τ k*profile (2*Real.pi*((k:ℝ)*q))

def radialCost (s : Finset ℕ) (n : ℕ) (τ θ η : ℝ) :=
  ∑ k ∈ s, weight η k*correction n k τ θ

theorem attenuation_bounds (τ : ℝ) (hτ : 0 ≤ τ) (k : ℕ) :
    0 ≤ attenuation τ k ∧ attenuation τ k ≤ 1 := by
  have h := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg k)) hτ)
  unfold attenuation
  constructor
  · positivity
  · linarith

theorem sum_block_transfer (s : Finset ℕ) (n : ℕ) (τ ξ η : ℝ) (hτ : 0 ≤ τ) (q : ℚ) :
    (∑ k ∈ s, weight η k*blockBound n k τ (2*Real.pi*ξ)) ≤
      nominalCost s q τ η+radialCost s n τ (2*Real.pi*ξ) η+
      ∑ k ∈ s, weight η k*
        |profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
  have ht (k : ℕ) : attenuation τ k*profile (2*Real.pi*((k:ℝ)*ξ)) ≤
      attenuation τ k*profile (2*Real.pi*((k:ℝ)*q))+
        |profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
    have ha := attenuation_bounds τ hτ k
    have hd := neg_le_abs (profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ)))
    have hm := mul_le_mul_of_nonneg_left (show profile (2*Real.pi*((k:ℝ)*ξ)) ≤
      profile (2*Real.pi*((k:ℝ)*q))+
      |profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| by linarith) ha.1
    have hh := mul_le_mul_of_nonneg_right ha.2
      (abs_nonneg (profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))))
    nlinarith
  have he (k : ℕ) : blockBound n k τ (2*Real.pi*ξ) =
      attenuation τ k*profile (2*Real.pi*((k:ℝ)*ξ))+correction n k τ (2*Real.pi*ξ) := by
    unfold blockBound attenuation correction
    rw [show (k:ℝ)*(2*Real.pi*ξ) = 2*Real.pi*((k:ℝ)*ξ) by ring]
    ring
  have hblock (k : ℕ) : weight η k*blockBound n k τ (2*Real.pi*ξ) ≤
      weight η k*attenuation τ k*profile (2*Real.pi*((k:ℝ)*q))+
      weight η k*correction n k τ (2*Real.pi*ξ)+
      weight η k*|profile (2*Real.pi*((k:ℝ)*q))-profile (2*Real.pi*((k:ℝ)*ξ))| := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (ht k)
      (show 0 ≤ weight η k by unfold weight; positivity)
    nlinarith
  have hh := Finset.sum_le_sum (s := s) (fun k _ => hblock k)
  simpa only [Finset.sum_add_distrib,nominalCost,radialCost] using hh

theorem coprime_sines (ξ : ℝ) (Q K : ℕ) (hQ : 0 < Q) (q : ℚ)
    (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5) (hKQ : 5*K < Q)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 K) (hkn : ¬ q.den ∣ k) :
    Real.sin ((k:ℝ)*(2*Real.pi*ξ)/2) ≠ 0 ∧
      Real.sin (5*((k:ℝ)*(2*Real.pi*ξ))/2) ≠ 0 := by
  have hk' := Finset.mem_Icc.mp hk
  have h1 := LargeDenominatorVariation.sine_frequency_ne_zero ξ Q hQ q hq k hkn (by omega)
  have h5kn : ¬ q.den ∣ 5*k := fun h => hkn (hb5.dvd_mul_left.mp h)
  have h5 := LargeDenominatorVariation.sine_frequency_ne_zero ξ Q hQ q hq (5*k) h5kn (by omega)
  constructor
  · rwa [show (k:ℝ)*(2*Real.pi*ξ)/2 = Real.pi*((k:ℝ)*ξ) by ring]
  · rw [show 5*((k:ℝ)*(2*Real.pi*ξ))/2 = Real.pi*(((5*k:ℕ):ℝ)*ξ) by push_cast; ring]
    exact h5

theorem divisible_sines (ξ : ℝ) (Q K : ℕ) (hQ : 0 < Q) (q : ℚ)
    (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B) (hKQ : K < Q)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 K) (hkn : ¬ B ∣ k) :
    Real.sin ((k:ℝ)*(2*Real.pi*ξ)/2) ≠ 0 ∧
      Real.sin (5*((k:ℝ)*(2*Real.pi*ξ))/2) ≠ 0 := by
  have hk' := Finset.mem_Icc.mp hk
  have hbkn : ¬ q.den ∣ k := by
    intro h
    exact hkn (dvd_trans (show B ∣ q.den by rw [hb]; exact dvd_mul_left _ _) h)
  have h1 := LargeDenominatorVariation.sine_frequency_ne_zero ξ Q hQ q hq k hbkn (by omega)
  have h5 := FiveDivisibleVariation.five_sine_ne_zero ξ Q hQ q hq B k hb hkn (by omega)
  constructor
  · rwa [show (k:ℝ)*(2*Real.pi*ξ)/2 = Real.pi*((k:ℝ)*ξ) by ring]
  · rwa [show 5*((k:ℝ)*(2*Real.pi*ξ))/2 = Real.pi*(5*(k:ℝ)*ξ) by ring]

theorem coprime_norm_upper (n : ℕ) (hn : 0 < n) (Q K : ℕ) (hQ : 0 < Q)
    (τ ξ η : ℝ) (hτ : 0 ≤ τ) (hη : 0 < η) (q : ℚ)
    (hq : DirichletCover.Near ξ Q q) (hb5 : q.den.Coprime 5) (hKQ : 5*K < Q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ (2*Real.pi*ξ)) (Borwein.polynomial n)‖ ≤
      Real.exp (2*η*n+(4*n)*(∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ k), weight η k)+
        nominalCost (GeneralDenominatorVariation.nonresonant q K) q τ η+
        radialCost (GeneralDenominatorVariation.nonresonant q K) n τ (2*Real.pi*ξ) η+
        (GeneralDenominatorVariation.multiplicity q K:ℝ)*(Real.pi^3*q.den/(30*Q)*
          (1/(1-(K:ℝ)/Q)+6/(1-5*(K:ℝ)/Q)))+tail n K η) := by
  have hs := coprime_sines ξ Q K hQ q hq hb5 hKQ
  have h := FiniteBlockLocalization.polynomial_norm_split n hn K τ (2*Real.pi*ξ) η hτ hη
    (fun k => q.den ∣ k) (fun k hk hkn => (hs k hk hkn).1) (fun k hk hkn => (hs k hk hkn).2)
  have ht := (sum_block_transfer (GeneralDenominatorVariation.nonresonant q K) n τ ξ η hτ q).trans
    (add_le_add le_rfl (GeneralDenominatorVariation.unified_profile_sum ξ η hη.le Q K hQ q hq hb5 hKQ))
  apply h.trans
  apply Real.exp_le_exp.mpr
  change _ ≤ _ at ht
  dsimp [GeneralDenominatorVariation.nonresonant] at ht ⊢
  linarith

theorem divisible_norm_upper (n : ℕ) (hn : 0 < n) (Q K : ℕ) (hQ : 0 < Q)
    (τ ξ η : ℝ) (hτ : 0 ≤ τ) (hη : 0 < η) (q : ℚ)
    (hq : DirichletCover.Near ξ Q q) (B : ℕ) (hb : q.den = 5*B) (hKQ : K < Q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ (2*Real.pi*ξ)) (Borwein.polynomial n)‖ ≤
      Real.exp (2*η*n+(4*n)*(∑ k ∈ (Finset.Icc 1 K).filter (fun k => B ∣ k), weight η k)+
        nominalCost (FiveDivisibleVariation.nonresonant B K) q τ η+
        radialCost (FiveDivisibleVariation.nonresonant B K) n τ (2*Real.pi*ξ) η+
        Real.pi^3*q.den/(30*Q*(1-(K:ℝ)/Q))*
          ((GeneralDenominatorVariation.multiplicity q K:ℝ)+(2*ResidueBlockCount.blocks K B:ℕ)/4)+
        tail n K η) := by
  have hs := divisible_sines ξ Q K hQ q hq B hb hKQ
  have h := FiniteBlockLocalization.polynomial_norm_split n hn K τ (2*Real.pi*ξ) η hτ hη
    (fun k => B ∣ k) (fun k hk hkn => (hs k hk hkn).1) (fun k hk hkn => (hs k hk hkn).2)
  have ht := (sum_block_transfer (FiveDivisibleVariation.nonresonant B K) n τ ξ η hτ q).trans
    (add_le_add le_rfl (FiveDivisibleProfile.profile_sum ξ η hη.le Q K hQ q hq B hb hKQ))
  apply h.trans
  apply Real.exp_le_exp.mpr
  dsimp [FiveDivisibleVariation.nonresonant] at ht ⊢
  linarith

end
end Borwein.FiniteBlockDenominators
