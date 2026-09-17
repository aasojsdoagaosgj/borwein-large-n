import Borwein.GapSumData

namespace Borwein.GapSumBridge
noncomputable section
open scoped BigOperators
open Borwein.GapSumData

theorem min_scale (x : ℝ) : min 2 (x/2000) = min 4000 x/2000 := by
  by_cases hx : x ≤ 4000
  · rw [min_eq_right (by linarith), min_eq_right hx]
  · rw [min_eq_left (by linarith), min_eq_left (le_of_not_ge hx)]
    norm_num

theorem profile_argument (d : Fin 4) (i : ℕ) :
    min 2 (((d:ℝ)+1)*(6/5)*Borwein.ResonantCertificate.uniformGrid 400 (i+1)) =
      (A d i:ℝ)/2000 := by
  have he : ((d:ℝ)+1)*(6/5)*Borwein.ResonantCertificate.uniformGrid 400 (i+1) =
      6*((d:ℝ)+1)*((i:ℝ)+1)/2000 := by
    simp only [Borwein.ResonantCertificate.uniformGrid, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [he, min_scale]
  simp only [A, Nat.cast_min, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

theorem term_cast (d : Fin 4) (i : ℕ) :
    (term d i:ℝ)/(denominator:ℝ) =
      (Borwein.CheckedWeights.lower d i-Borwein.CheckedWeights.upper d (i+1))*
        Borwein.ResonantCertificate.uniformGrid 400 (i+1)*
        Borwein.SincBounds.profile
          (min 2 (((d:ℝ)+1)*(6/5)*Borwein.ResonantCertificate.uniformGrid 400 (i+1))) := by
  rw [profile_argument]
  unfold term Borwein.CheckedWeights.lower Borwein.CheckedWeights.upper
    Borwein.ResonantCertificate.uniformGrid Borwein.SincBounds.profile
  simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_pow, Int.cast_add,
    Int.cast_one, Int.cast_ofNat, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  norm_num only [denominator, Borwein.RoundedWeightData.W, Nat.cast_ofNat]
  ring

theorem lowerGap_eq_total :
    Borwein.CheckedWeights.lowerGap = (total:ℝ)/(denominator:ℝ) := by
  unfold Borwein.CheckedWeights.lowerGap Borwein.FiniteGapBounds.lowerCertificate total
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  exact (term_cast d i).symm

theorem partition (f : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range (25*n), f i) =
      ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range 25, f (25*k+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ (n := n)]

theorem total_eq_blocks : total = ∑ k ∈ Finset.range 16, block k := by
  unfold total block
  have h (d : Fin 4) := partition (term d) 16
  simp only [show 25*16=400 by norm_num] at h
  simp_rw [h]
  rw [Finset.sum_comm]

end
end Borwein.GapSumBridge
