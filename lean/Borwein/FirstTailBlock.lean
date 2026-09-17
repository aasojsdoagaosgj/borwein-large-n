import Borwein.StableFirstTail
import Borwein.CertifiedFiveDissection

set_option autoImplicit false

namespace Borwein.FirstTailBlock
noncomputable section
open PowerSeries StableBorweinSeries

def numerator : ℤ⟦X⟧ := (rrSeries 1)^2-rrSeries 1*rrSeries 2-(rrSeries 2)^2
def shifted (n K a i d : ℕ) : ℤ :=
  if 5*(n+i)+d ≤ 5*n+5*K+a then stableCoeff (5*n+5*K+a-(5*(n+i)+d)) else 0

theorem shifted_le (n K a i d : ℕ) (hi : i ≤ K) (hd : d ≤ a) :
    shifted n K a i d=stableCoeff (5*(K-i)+(a-d)) := by
  unfold shifted
  rw [if_pos (by omega)]
  congr 1
  omega

theorem shifted_weak (n K a i d : ℕ)
    (hweak : (a=3 ∧ d=4) ∨ (a=4 ∧ d=1)) : shifted n K a i d=0 := by
  unfold shifted
  split_ifs with h
  · apply CertifiedLowWeakZero.stable_weak_zero
    rcases hweak with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> omega
  · rfl

theorem block_as_four (n K a i : ℕ) :
    (∑ b : Fin 4, if Borwein.exponent (n+i) b ≤ 5*n+5*K+a then
      stableCoeff (5*n+5*K+a-Borwein.exponent (n+i) b) else 0)=
      shifted n K a i 1+shifted n K a i 2+shifted n K a i 3+shifted n K a i 4 := by
  simp only [Fin.sum_univ_succ]
  unfold Borwein.exponent shifted
  simp only [Fin.val_zero, Fin.val_succ, Nat.add_zero, Nat.zero_add, Nat.add_assoc, Nat.reduceAdd]
  ring

theorem block_value (n K a i : ℕ) (ha : a=3 ∨ a=4) (hi : i ≤ K) :
    (∑ b : Fin 4, if Borwein.exponent (n+i) b ≤ 5*n+5*K+a then
      stableCoeff (5*n+5*K+a-Borwein.exponent (n+i) b) else 0)=coeff (K-i) numerator := by
  rw [block_as_four]
  rcases ha with rfl | rfl
  · rw [shifted_le n K 3 i 1 hi (by omega), shifted_le n K 3 i 2 hi (by omega),
      shifted_le n K 3 i 3 hi (by omega), shifted_weak n K 3 i 4 (by omega)]
    norm_num only
    simp only [Nat.add_zero]
    rw [StableOuterCoefficient.stable_class_two,
      StableMiddleCoefficient.stable_class_one, StableOuterCoefficient.stable_class_zero]
    simp only [numerator, map_sub]
    ring
  · rw [shifted_weak n K 4 i 1 (by omega), shifted_le n K 4 i 2 hi (by omega),
      shifted_le n K 4 i 3 hi (by omega), shifted_le n K 4 i 4 hi (by omega)]
    norm_num only
    simp only [Nat.add_zero]
    rw [StableOuterCoefficient.stable_class_two,
      StableMiddleCoefficient.stable_class_one, StableOuterCoefficient.stable_class_zero]
    simp only [numerator, map_sub]
    ring

theorem block_outside (n K a i : ℕ) (ha : a ≤ 4) (hi : K < i) :
    (∑ b : Fin 4, if Borwein.exponent (n+i) b ≤ 5*n+5*K+a then
      stableCoeff (5*n+5*K+a-Borwein.exponent (n+i) b) else 0)=0 := by
  apply Finset.sum_eq_zero
  intro b hb
  rw [if_neg (by unfold Borwein.exponent; omega)]

theorem tail_sum (n K a : ℕ) (ha : a=3 ∨ a=4) :
    StableFirstTail.tailCoefficient n (5*n+5*K+a)=
      ∑ i ∈ Finset.range (K+1), coeff (K-i) numerator := by
  unfold StableFirstTail.tailCoefficient
  have he := Finset.sum_subset (f := fun i => ∑ b : Fin 4,
      if Borwein.exponent (n+i) b ≤ 5*n+5*K+a then
        stableCoeff (5*n+5*K+a-Borwein.exponent (n+i) b) else 0)
    (Finset.range_mono (show K+1 ≤ 5*n+5*K+a+1 by omega))
    (by
      intro i hi hnot
      apply block_outside n K a i (by omega)
      simp only [Finset.mem_range] at hnot
      omega)
  rw [← he]
  apply Finset.sum_congr rfl
  intro i hi
  exact block_value n K a i ha (by simp only [Finset.mem_range] at hi; omega)

end
end Borwein.FirstTailBlock
