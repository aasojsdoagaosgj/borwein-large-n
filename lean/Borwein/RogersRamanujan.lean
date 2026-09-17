import Borwein.Hypergeometric
import Mathlib.Tactic

/-!
# A concrete coefficientwise Rogers--Ramanujan recurrence

For fixed degree `k`, `rrCoeff t k` is the include/exclude recurrence model for
partitions of `k` into distinct parts at least `t` with gaps at least two,
splitting according to whether the smallest available part `t` is used.  The
recursive definition itself is the coefficient form of (3.1).  The exceptional index `t=0` is included only
so the sequence satisfies the abstract recurrence at every natural index;
the manuscript uses indices `t ≥ 1`.  Identification with the manuscript's
hypergeometric definition of `R_t` is a separate, not-yet-formalized theorem.
-/

namespace Borwein

open Finset PowerSeries

/-- Coefficients determined by the Rogers--Ramanujan include/exclude recurrence. -/
def rrCoeff (t k : ℕ) : ℕ :=
  if t = 0 then rrCoeff 1 k + rrCoeff 2 k
  else if k = 0 then 1
  else if k < t then 0
  else rrCoeff (t + 1) k + rrCoeff (t + 2) (k - t)
termination_by k + 1 - t
decreasing_by all_goals omega

/-- Positive-index series have constant coefficient one. -/
theorem rrCoeff_zero_of_pos (t : ℕ) (ht : 0 < t) : rrCoeff t 0 = 1 := by
  rw [rrCoeff]
  simp [ht.ne']

/-- No positive degree below the least allowed part can occur. -/
theorem rrCoeff_eq_zero_of_pos_lt {t k : ℕ} (hk : 0 < k) (hkt : k < t) :
    rrCoeff t k = 0 := by
  have ht : t ≠ 0 := by omega
  rw [rrCoeff]
  simp [ht, hk.ne', hkt]

/-- The defining coefficient recurrence, including the harmless `t=0` extension. -/
theorem rrCoeff_recurrence (t k : ℕ) :
    rrCoeff t k = rrCoeff (t + 1) k +
      if t ≤ k then rrCoeff (t + 2) (k - t) else 0 := by
  by_cases ht : t = 0
  · subst t
    rw [rrCoeff]
    simp
  by_cases hk : k = 0
  · subst k
    rw [rrCoeff]
    simp [ht, rrCoeff_zero_of_pos]
  by_cases hkt : k < t
  · rw [rrCoeff_eq_zero_of_pos_lt (Nat.pos_of_ne_zero hk) hkt]
    rw [rrCoeff_eq_zero_of_pos_lt (Nat.pos_of_ne_zero hk) (by omega : k < t + 1)]
    simp [Nat.not_le_of_gt hkt]
  · have hle : t ≤ k := Nat.le_of_not_gt hkt
    rw [rrCoeff]
    simp [ht, hk, hkt, hle]

/-- The corresponding integer formal power series. -/
noncomputable def rrSeries (t : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun k ↦ (rrCoeff t k : ℤ)

@[simp] theorem coeff_rrSeries (t k : ℕ) :
    coeff k (rrSeries t) = rrCoeff t k := by
  simp [rrSeries]

/-- Formal-power-series form of (3.1). -/
theorem rrSeries_recurrence (t : ℕ) :
    rrSeries t = rrSeries (t + 1) + X ^ t * rrSeries (t + 2) := by
  ext k
  rw [map_add, coeff_X_pow_mul', coeff_rrSeries, coeff_rrSeries]
  rw [rrCoeff_recurrence]
  split_ifs with h
  · simp
  · simp

/-- The concrete sequence satisfies the abstract recurrence used above. -/
theorem rrSeries_isRRRecurrence :
    RRRecurrence (X : ℤ⟦X⟧) rrSeries :=
  rrSeries_recurrence

/-- Nonnegativity is built into the natural-number coefficient model. -/
theorem coeffNonneg_rrSeries (t : ℕ) : CoeffNonneg (rrSeries t) := by
  intro k
  rw [coeff_rrSeries]
  exact Int.natCast_nonneg _

theorem constantCoeff_rrSeries (t : ℕ) (ht : 0 < t) : coeff 0 (rrSeries t) = 1 := by
  rw [coeff_rrSeries, rrCoeff_zero_of_pos t ht]
  norm_num

theorem coeff_one_rrSeries_two : coeff 1 (rrSeries 2) = 0 := by
  rw [coeff_rrSeries]
  simp [rrCoeff_eq_zero_of_pos_lt (by norm_num) (by norm_num : 1 < 2)]

theorem coeff_one_rrSeries_three : coeff 1 (rrSeries 3) = 0 := by
  rw [coeff_rrSeries]
  simp [rrCoeff_eq_zero_of_pos_lt (by norm_num) (by norm_num : 1 < 3)]

/-- The coefficientwise hypergeometric definition (2.2) agrees with the
include/exclude recurrence model at every positive index. -/
theorem coeff_hyperSeries_eq_rrSeries (t k : ℕ) (ht : 0 < t) :
    coeff k (hyperSeries t) = coeff k (rrSeries t) := by
  by_cases hk0 : k = 0
  · subst k
    rw [coeff_zero_hyperSeries, coeff_rrSeries, rrCoeff_zero_of_pos t ht]
    norm_num
  by_cases hkt : k < t
  · rw [coeff_hyperSeries_eq_zero_of_pos_lt (Nat.pos_of_ne_zero hk0) hkt]
    rw [coeff_rrSeries]
    simp [rrCoeff_eq_zero_of_pos_lt (Nat.pos_of_ne_zero hk0) hkt]
  · have htk : t ≤ k := Nat.le_of_not_gt hkt
    have ih1 := coeff_hyperSeries_eq_rrSeries (t + 1) k (by omega)
    have ih2 := coeff_hyperSeries_eq_rrSeries (t + 2) (k - t) (by omega)
    have hhyper := congrArg (fun f : ℤ⟦X⟧ ↦ coeff k f) (hyperSeries_recurrence t ht)
    have hrr := congrArg (fun f : ℤ⟦X⟧ ↦ coeff k f) (rrSeries_recurrence t)
    simp only [map_add, coeff_X_pow_mul', if_pos htk] at hhyper hrr
    rw [ih1, ih2] at hhyper
    exact hhyper.trans hrr.symm
termination_by k + 1 - t
decreasing_by all_goals omega

/-- Formal identification of the two definitions of `R_t` for `t≥1`. -/
theorem hyperSeries_eq_rrSeries (t : ℕ) (ht : 0 < t) :
    hyperSeries t = rrSeries t := by
  ext k
  exact coeff_hyperSeries_eq_rrSeries t k ht

/-- A singleton part proves strict positivity whenever the requested degree is
at least the least allowed positive part. -/
theorem rrCoeff_pos_of_pos_le (t k : ℕ) (ht : 0 < t) (htk : t ≤ k) :
    0 < rrCoeff t k := by
  by_cases heq : t = k
  · subst k
    rw [rrCoeff_recurrence]
    rw [rrCoeff_eq_zero_of_pos_lt ht (by omega : t < t + 1)]
    simp [rrCoeff_zero_of_pos]
  · have ht1k : t + 1 ≤ k := by omega
    have ih := rrCoeff_pos_of_pos_le (t + 1) k (by omega) ht1k
    rw [rrCoeff_recurrence]
    exact Nat.add_pos_left ih _
termination_by k + 1 - t
decreasing_by omega

theorem coeff_rrSeries_pos_of_pos_le (t k : ℕ) (ht : 0 < t) (htk : t ≤ k) :
    0 < coeff k (rrSeries t) := by
  rw [coeff_rrSeries]
  exact_mod_cast rrCoeff_pos_of_pos_le t k ht htk

/-- The `j=0` product in (3.4) is strictly positive from degree two onward. -/
theorem coeff_rrSeries_two_mul_three_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < coeff K (rrSeries 2 * rrSeries 3) := by
  rw [coeff_mul]
  have hterms : ∀ p ∈ antidiagonal K,
      0 ≤ coeff p.1 (rrSeries 2) * coeff p.2 (rrSeries 3) := by
    intro p hp
    exact mul_nonneg (coeffNonneg_rrSeries 2 p.1) (coeffNonneg_rrSeries 3 p.2)
  have hle := Finset.single_le_sum
    (s := antidiagonal K)
    (f := fun p ↦ coeff p.1 (rrSeries 2) * coeff p.2 (rrSeries 3))
    hterms (mem_antidiagonal.mpr (by simp) : (K, 0) ∈ antidiagonal K)
  have hselected :
      0 < coeff K (rrSeries 2) * coeff 0 (rrSeries 3) := by
    rw [constantCoeff_rrSeries 3 (by norm_num)]
    simpa using coeff_rrSeries_pos_of_pos_le 2 K (by norm_num) hK
  exact hselected.trans_le hle

/-- The concrete coefficient sequence corresponding to `d_K` in (3.4). -/
noncomputable def concreteDCoeff (K : ℕ) : ℤ := dCoeff rrSeries K

theorem concreteDCoeff_nonneg (K : ℕ) : 0 ≤ concreteDCoeff K :=
  dCoeff_nonneg rrSeries rrSeries_isRRRecurrence coeffNonneg_rrSeries K

theorem concreteDCoeff_zero : concreteDCoeff 0 = 1 :=
  dCoeff_zero rrSeries rrSeries_isRRRecurrence
    (constantCoeff_rrSeries 2 (by norm_num)) (constantCoeff_rrSeries 3 (by norm_num))

theorem concreteDCoeff_one : concreteDCoeff 1 = 0 :=
  dCoeff_one rrSeries rrSeries_isRRRecurrence
    (constantCoeff_rrSeries 2 (by norm_num)) (constantCoeff_rrSeries 3 (by norm_num))
    coeff_one_rrSeries_two coeff_one_rrSeries_three

/-- The strict positivity assertion `d_K>0` for every `K≥2`. -/
theorem concreteDCoeff_pos (K : ℕ) (hK : 2 ≤ K) : 0 < concreteDCoeff K :=
  dCoeff_pos_of_baseProduct_pos rrSeries rrSeries_isRRRecurrence coeffNonneg_rrSeries
    (coeff_rrSeries_two_mul_three_pos K hK)

/-- The exact hypergeometric series `ᵍ` displayed in (3.4), with
`g=R₁` and `h=R₂`. -/
noncomputable def hypergeometricD : ℤ⟦X⟧ :=
  geometricSeries *
    (hyperSeries 1 * hyperSeries 2 + hyperSeries 2 ^ 2 - hyperSeries 1 ^ 2)

/-- The displayed numerator in (3.4) agrees with the kernel quotient already
constructed from the recurrence. -/
theorem hypergeometricD_eq_nonnegativeKernelSeries :
    hypergeometricD = nonnegativeKernelSeries rrSeries := by
  unfold hypergeometricD
  rw [hyperSeries_eq_rrSeries 1 (by norm_num),
    hyperSeries_eq_rrSeries 2 (by norm_num)]
  unfold nonnegativeKernelSeries kernelQuotient kernel
  rw [rrSeries_recurrence 1]
  simp only [pow_one]
  ring

/-- Consequently `ᵍ` is exactly the quotient of its numerator by `1-X`. -/
theorem one_sub_X_mul_hypergeometricD :
    (1 - X) * hypergeometricD =
      hyperSeries 1 * hyperSeries 2 + hyperSeries 2 ^ 2 - hyperSeries 1 ^ 2 := by
  unfold hypergeometricD
  rw [show (1 - X) *
      (geometricSeries *
        (hyperSeries 1 * hyperSeries 2 + hyperSeries 2 ^ 2 - hyperSeries 1 ^ 2)) =
      (geometricSeries * (1 - X)) *
        (hyperSeries 1 * hyperSeries 2 + hyperSeries 2 ^ 2 - hyperSeries 1 ^ 2) by ring]
  rw [geometricSeries_mul_one_sub_X, one_mul]

/-- Coefficients of the actual hypergeometric `ᵍ`. -/
noncomputable def hypergeometricDCoeff (K : ℕ) : ℤ := coeff K hypergeometricD

theorem hypergeometricDCoeff_eq_concreteDCoeff (K : ℕ) :
    hypergeometricDCoeff K = concreteDCoeff K := by
  unfold hypergeometricDCoeff concreteDCoeff dCoeff
  rw [hypergeometricD_eq_nonnegativeKernelSeries]

theorem hypergeometricDCoeff_zero : hypergeometricDCoeff 0 = 1 := by
  rw [hypergeometricDCoeff_eq_concreteDCoeff, concreteDCoeff_zero]

theorem hypergeometricDCoeff_one : hypergeometricDCoeff 1 = 0 := by
  rw [hypergeometricDCoeff_eq_concreteDCoeff, concreteDCoeff_one]

theorem hypergeometricDCoeff_pos (K : ℕ) (hK : 2 ≤ K) :
    0 < hypergeometricDCoeff K := by
  rw [hypergeometricDCoeff_eq_concreteDCoeff]
  exact concreteDCoeff_pos K hK

end Borwein
