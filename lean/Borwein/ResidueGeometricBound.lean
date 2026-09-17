import Borwein.WeightedResidueBound
import Borwein.CoprimeFrequencyResidues

set_option autoImplicit false

namespace Borwein.ResidueGeometricBound
noncomputable section
open Complex AngularKernel FiniteBlockLocalization ResonantGeometricSum ZeroPoleBudget
  NonresonantGeometricBound GeneralDenominatorVariation

theorem point_bound (n M Q k : ℕ) (τ θ : ℝ) (q : ℚ) (hQ : 0 < Q) (hτ : 0 ≤ τ)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hr : (k:ℝ)/Q < DirichletCover.residue q k) :
    ‖geometricSum M ((point n τ θ)^k)‖ ≤ (q.den:ℝ)/(2*(DirichletCover.residue q k-(k:ℝ)/Q)) := by
  have hs := residue_sine_lower (θ/(2*Real.pi)) Q hQ q hq k
  have he : Real.pi*((k:ℝ)*(θ/(2*Real.pi))) = (k:ℝ)*θ/2 := by field_simp
  rw [he] at hs
  have hpos : 0 < 2*(DirichletCover.residue q k-(k:ℝ)/Q)/(q.den:ℝ) := by positivity
  rw [point_pow]
  apply (geometric_bound M (Real.exp (-((k:ℝ)*τ/(5*n)))) ((k:ℝ)*θ)
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) (hpos.trans_le hs)).trans
  have h := one_div_le_one_div_of_le hpos hs
  convert h using 1 <;> field_simp

def frequencyCost (q : ℚ) (K Q d : ℕ) (η : ℝ) : ℝ :=
  (q.den:ℝ)/2*(DilogarithmUpper.radial (2*η)/2+
    (1/2+(d:ℝ)/(Q*(1-(d:ℝ)*K/Q)))*(GeneralDenominatorVariation.multiplicity q K:ℝ)*(Real.pi^2/6))

theorem weighted_frequency (n M Q K d : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hcut : d*K < Q) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hd : d.Coprime q.den) :
    ‖∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ d*k),
      (weight η k:ℂ)*geometricSum M ((point n τ θ)^(d*k))‖ ≤ frequencyCost q K Q d η := by
  let s := (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ d*k)
  have hk (k : ℕ) (hks : k ∈ s) : 0 < k ∧ k ≤ K := by
    have h := Finset.mem_Icc.mp (Finset.mem_filter.mp hks).1
    exact ⟨by omega,h.2⟩
  have hr (k : ℕ) (hks : k ∈ s) : 1 ≤ DirichletCover.residue q (d*k) :=
    DirichletCover.residue_ge_one q (d*k) (Finset.mem_filter.mp hks).2
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have ht (k : ℕ) (hks : k ∈ s) :
      ‖(weight η k:ℂ)*geometricSum M ((point n τ θ)^(d*k))‖ ≤
        (q.den:ℝ)/2*(weight η k/(DirichletCover.residue q (d*k)-(d:ℝ)*k/Q)) := by
    have hdk : d*k < Q := lt_of_le_of_lt (Nat.mul_le_mul_left d (hk k hks).2) hcut
    have hfrac : ((d*k:ℕ):ℝ)/Q < 1 := (div_lt_one hQ').mpr (by exact_mod_cast hdk)
    have hp := point_bound n M Q (d*k) τ θ q hQ hτ hq (hfrac.trans_le (hr k hks))
    have hw : 0 ≤ weight η k := by unfold weight; positivity
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_left hp hw).trans_eq
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hh := WeightedResidueBound.perturbed_sum s η Q K d (fun k => DirichletCover.residue q (d*k)) hη hQ hcut hk hr
  have hi := CoprimeFrequencyResidues.inverse_square_subset q d K s (Finset.filter_subset _ _) hd
  have hcoef : 0 ≤ 1/2+(d:ℝ)/(Q*(1-(d:ℝ)*K/Q)) := by
    have hc : (d:ℝ)*K/Q < 1 := (div_lt_one hQ').mpr (by exact_mod_cast hcut)
    positivity
  have hm := mul_le_mul_of_nonneg_left hi hcoef
  have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum ht)
  rw [← Finset.mul_sum] at hsum
  apply hsum.trans
  unfold frequencyCost
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (q.den:ℝ)/2)
  nlinarith

theorem nonresonant_bound (n Q K : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hcut : 5*K < Q) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den.Coprime 5) :
    ‖ResonantFourierSplit.nonresonant n K (point n τ θ) η q‖ ≤
      frequencyCost q K Q 1 η+frequencyCost q K Q 5 η := by
  have h1 := weighted_frequency n (5*n) Q K 1 τ θ η q hQ (by omega) hτ hη hq (by simp)
  have h5 := weighted_frequency n n Q K 5 τ θ η q hQ hcut hτ hη hq hb.symm
  simp only [one_mul] at h1
  unfold ResonantFourierSplit.nonresonant
  exact (norm_sub_le _ _).trans (add_le_add h1 h5)

end
end Borwein.ResidueGeometricBound
