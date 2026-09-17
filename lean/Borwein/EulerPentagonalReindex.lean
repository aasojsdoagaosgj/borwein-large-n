import Borwein.EulerPentagonalCenter

set_option autoImplicit false

namespace Borwein.EulerPentagonalReindex
noncomputable section
open Complex EulerQBinomial EulerPentagonalCenter EndpointEulerTail

def centered (q : ℂ) (n : ℕ) (j : ℤ) : ℂ :=
  if -(n:ℤ) ≤ j ∧ j ≤ (n:ℤ) then
    gaussian (q^3) (2*n) ((n:ℤ)+j).toNat*atom q j else 0

theorem centered_inside (q : ℂ) (n : ℕ) (j : ℤ) (hj : -(n:ℤ) ≤ j ∧ j ≤ (n:ℤ)) :
    centered q n j=gaussian (q^3) (2*n) ((n:ℤ)+j).toNat*atom q j := by
  simp only [centered, if_pos hj]

theorem centered_outside (q : ℂ) (n : ℕ) (j : ℤ) (hj : ¬ (-(n:ℤ) ≤ j ∧ j ≤ (n:ℤ))) :
    centered q n j=0 := by simp only [centered, if_neg hj]

theorem centerTerm_eq (q : ℂ) (n k : ℕ) (hk : k ≤ 2*n) :
    centerTerm q n k=centered q n ((k:ℤ)-(n:ℤ)) := by
  have hi : -(n:ℤ) ≤ (k:ℤ)-(n:ℤ) ∧ (k:ℤ)-(n:ℤ) ≤ (n:ℤ) := by omega
  rw [centered_inside q n _ hi]
  have he : ((n:ℤ)+((k:ℤ)-(n:ℤ))).toNat=k := by omega
  rw [he]
  rfl

theorem finite_reindex (q : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (2*n+1), centerTerm q n k)=
      ∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), centered q n j := by
  apply Finset.sum_bij (fun (k : ℕ) _ => (k:ℤ)-(n:ℤ))
  · intro k hk
    have hkn := Finset.mem_range.mp hk
    exact Finset.mem_Icc.mpr (by omega)
  · intro k hk l hl he
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨((n:ℤ)+j).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    omega
  · intro k hk
    exact centerTerm_eq q n k (by have hh := Finset.mem_range.mp hk; omega)

theorem tsum_centered (q : ℂ) (n : ℕ) :
    (∑' j : ℤ, centered q n j)=∑ j ∈ Finset.Icc (-(n:ℤ)) (n:ℤ), centered q n j := by
  apply tsum_eq_sum
  intro j hj
  exact centered_outside q n j (by simpa only [Finset.mem_Icc] using hj)

/-- The exact finite Euler identity expressed as a sum over one fixed integer index set. -/
theorem finite_euler_tsum (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    finiteEuler (3*n) q=finiteEuler n (q^3)*(∑' j : ℤ, centered q n j) := by
  rw [finite_centered q n hq hq0, finite_reindex, tsum_centered]

end
end Borwein.EulerPentagonalReindex
