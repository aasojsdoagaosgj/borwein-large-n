import Borwein.ReducedFiveFrequency

set_option autoImplicit false

namespace Borwein.LargeDivisibleNonresonant
noncomputable section
open Complex FiniteBlockLocalization ResonantGeometricSum ZeroPoleBudget ResidueGeometricBound

theorem scaled_point (n M Q B k : ℕ) (τ θ : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hkQ : k < Q) (hτ : 0 ≤ τ)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5*B)
    (hk : ¬ ((5:ℚ)*q).den ∣ k) :
    ‖geometricSum M ((point n τ θ)^(5*k))‖ ≤
      (((5:ℚ)*q).den:ℝ)/(2*(DirichletCover.residue ((5:ℚ)*q) k-(k:ℝ)/Q)) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hr := DirichletCover.residue_ge_one ((5:ℚ)*q) k hk
  have hf : (k:ℝ)/Q < 1 := (div_lt_one hQ').mpr (by exact_mod_cast hkQ)
  have hp := point_bound n M Q (5*k) τ θ q hQ hτ hq (by
    rw [ReducedFiveFrequency.residue_scaled q B k hb]
    norm_num only [Nat.cast_mul,Nat.cast_ofNat]
    rw [mul_div_assoc]
    linarith)
  apply hp.trans_eq
  rw [ReducedFiveFrequency.residue_scaled q B k hb,ReducedFiveFrequency.scaled_den q B hb,hb]
  push_cast
  rw [show 5*DirichletCover.residue ((5:ℚ)*q) k-5*(k:ℝ)/Q =
    5*(DirichletCover.residue ((5:ℚ)*q) k-(k:ℝ)/Q) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem weighted_five (n M Q K B : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hcut : K < Q) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5*B) :
    ‖∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ 5*k),
      (weight η k:ℂ)*geometricSum M ((point n τ θ)^(5*k))‖ ≤ frequencyCost ((5:ℚ)*q) K Q 1 η := by
  let p : ℚ := 5*q
  let s := (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ 5*k)
  have hk (k : ℕ) (hks : k ∈ s) : 0 < k ∧ k ≤ K := by
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hks).1
    exact ⟨by omega,h.2⟩
  have hkn (k : ℕ) (hks : k ∈ s) : ¬ p.den ∣ k := by
    intro h
    exact (Finset.mem_filter.mp hks).2 ((ReducedFiveFrequency.resonance q B k hb).mpr h)
  have hr (k : ℕ) (hks : k ∈ s) : 1 ≤ DirichletCover.residue p k := DirichletCover.residue_ge_one p k (hkn k hks)
  have ht (k : ℕ) (hks : k ∈ s) :
      ‖(weight η k:ℂ)*geometricSum M ((point n τ θ)^(5*k))‖ ≤
        (p.den:ℝ)/2*(weight η k/(DirichletCover.residue p k-(k:ℝ)/Q)) := by
    have hp := scaled_point n M Q B k τ θ q hQ (lt_of_le_of_lt (hk k hks).2 hcut) hτ hq hb (hkn k hks)
    have hw : 0 ≤ weight η k := by unfold weight; positivity
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_left hp hw).trans_eq
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hh := WeightedResidueBound.perturbed_sum s η Q K 1 (fun k => DirichletCover.residue p k)
    hη hQ (by omega) hk hr
  have hi := CoprimeFrequencyResidues.inverse_square_subset p 1 K s (Finset.filter_subset _ _) (by simp)
  simp only [Nat.cast_one,one_mul] at hh hi
  have hcoef : 0 ≤ 1/2+(1:ℝ)/(Q*(1-(K:ℝ)/Q)) := by
    have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
    have hc : (K:ℝ)/Q < 1 := (div_lt_one hQ').mpr (by exact_mod_cast hcut)
    positivity
  have hm := mul_le_mul_of_nonneg_left hi hcoef
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum ht)
  rw [← Finset.mul_sum] at hsum
  apply hsum.trans
  unfold frequencyCost
  change _ ≤ (p.den:ℝ)/2*_
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (p.den:ℝ)/2)
  norm_num only [Nat.cast_one,one_mul]
  nlinarith

theorem nonresonant_bound (n Q K B : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hcut : K < Q) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5*B) :
    ‖ResonantFourierSplit.nonresonant n K (point n τ θ) η q‖ ≤
      frequencyCost q K Q 1 η+frequencyCost ((5:ℚ)*q) K Q 1 η := by
  have h1 := weighted_frequency n (5*n) Q K 1 τ θ η q hQ (by omega) hτ hη hq (by simp)
  have h5 := weighted_five n n Q K B τ θ η q hQ hcut hτ hη hq hb
  simp only [one_mul] at h1
  unfold ResonantFourierSplit.nonresonant
  exact (norm_sub_le _ _).trans (add_le_add h1 h5)

end
end Borwein.LargeDivisibleNonresonant
