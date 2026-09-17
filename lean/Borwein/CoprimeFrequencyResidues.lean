import Borwein.GeneralDenominatorVariation

set_option autoImplicit false

namespace Borwein.CoprimeFrequencyResidues
noncomputable section

theorem scaled_den (q : ℚ) (d : ℕ) (hd : d.Coprime q.den) : ((d:ℚ)*q).den = q.den := by
  rw [Rat.mul_den,Int.natAbs_mul]
  norm_num
  rw [(hd.mul_left q.reduced).gcd_eq_one,Nat.div_one]

theorem residue_scaled (q : ℚ) (d k : ℕ) (hd : d.Coprime q.den) :
    DirichletCover.residue q (d*k) = DirichletCover.residue ((d:ℚ)*q) k := by
  unfold DirichletCover.residue
  rw [scaled_den q d hd]
  push_cast
  rw [show (d:ℝ)*k*(q:ℝ) = (k:ℝ)*((d:ℝ)*q) by ring]

theorem inverse_square_injective (q : ℚ) (d K : ℕ) (hd : d.Coprime q.den) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(DirichletCover.residue q (d*k))^2) ≤ Real.pi^2/6 := by
  simp_rw [residue_scaled q d _ hd]
  exact ResidueMultiplicity.residue_inverse_square_sum ((d:ℚ)*q) K (by rwa [scaled_den q d hd])

theorem inverse_square_blocks (q : ℚ) (d K : ℕ) (hd : d.Coprime q.den) :
    (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(DirichletCover.residue q (d*k))^2) ≤
      (2*ResidueBlockCount.blocks K q.den:ℕ)*(Real.pi^2/6) := by
  simp_rw [residue_scaled q d _ hd]
  have h := ResidueBlockCount.residue_inverse_square_sum ((d:ℚ)*q) K
  rwa [scaled_den q d hd] at h

theorem inverse_square_subset (q : ℚ) (d K : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.Icc 1 K)
    (hd : d.Coprime q.den) :
    (∑ k ∈ s, (1:ℝ)/(DirichletCover.residue q (d*k))^2) ≤
      (GeneralDenominatorVariation.multiplicity q K:ℝ)*(Real.pi^2/6) := by
  have hsub : (∑ k ∈ s, (1:ℝ)/(DirichletCover.residue q (d*k))^2) ≤
      ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(DirichletCover.residue q (d*k))^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hs (fun k _ _ => by positivity)
  unfold GeneralDenominatorVariation.multiplicity
  split_ifs with hK
  · simpa using hsub.trans (inverse_square_injective q d K hd hK)
  · exact hsub.trans (inverse_square_blocks q d K hd)

end
end Borwein.CoprimeFrequencyResidues
