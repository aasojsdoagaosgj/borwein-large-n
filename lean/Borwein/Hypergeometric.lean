import Borwein.NonnegativeKernel
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-!
# Finite q-Pochhammer factors and the coefficientwise hypergeometric series

This file constructs the algebraic objects occurring in (2.2).  Infinite sums
are represented coefficientwise: for positive `t`, only indices `j ≤ k` can
contribute to the coefficient of degree `k`, so the defining sum is finite.
-/

namespace Borwein

open scoped BigOperators
open Finset PowerSeries

/-- The factor `1-X^r`. -/
noncomputable def qFactor (r : ℕ) : ℤ⟦X⟧ := 1 - X ^ r

/-- The finite q-Pochhammer product `(X;X)_j`. -/
noncomputable def qPochhammer (j : ℕ) : ℤ⟦X⟧ :=
  ∏ r ∈ Finset.range j, qFactor (r + 1)

/-- The inverse of `1-X^r`, constructed by expanding the geometric series. -/
noncomputable def qFactorInv (r : ℕ) (hr : r ≠ 0) : ℤ⟦X⟧ :=
  PowerSeries.expand r hr geometricSeries

theorem qFactorInv_mul_qFactor (r : ℕ) (hr : r ≠ 0) :
    qFactorInv r hr * qFactor r = 1 := by
  unfold qFactorInv qFactor
  rw [show (1 - X ^ r : ℤ⟦X⟧) = PowerSeries.expand r hr (1 - X) by simp]
  rw [← map_mul, geometricSeries_mul_one_sub_X]
  simp

/-- The reciprocal `1/(X;X)_j`, as a finite product of geometric series. -/
noncomputable def qPochhammerInv (j : ℕ) : ℤ⟦X⟧ :=
  ∏ r ∈ Finset.range j, qFactorInv (r + 1) (by omega)

theorem qPochhammer_succ (j : ℕ) :
    qPochhammer (j + 1) = qPochhammer j * qFactor (j + 1) := by
  simp [qPochhammer, Finset.prod_range_succ]

theorem qPochhammerInv_succ (j : ℕ) :
    qPochhammerInv (j + 1) =
      qPochhammerInv j * qFactorInv (j + 1) (by omega) := by
  simp [qPochhammerInv, Finset.prod_range_succ]

theorem qPochhammerInv_mul_qPochhammer (j : ℕ) :
    qPochhammerInv j * qPochhammer j = 1 := by
  induction j with
  | zero => simp [qPochhammerInv, qPochhammer]
  | succ j ih =>
      rw [qPochhammerInv_succ, qPochhammer_succ]
      rw [show qPochhammerInv j * qFactorInv (j + 1) (by omega) *
          (qPochhammer j * qFactor (j + 1)) =
          (qPochhammerInv j * qPochhammer j) *
            (qFactorInv (j + 1) (by omega) * qFactor (j + 1)) by ring]
      rw [ih, qFactorInv_mul_qFactor]
      simp

/-- Cancelling the newest q-Pochhammer factor lowers the reciprocal index. -/
theorem qFactor_mul_qPochhammerInv_succ (j : ℕ) :
    qFactor (j + 1) * qPochhammerInv (j + 1) = qPochhammerInv j := by
  rw [qPochhammerInv_succ]
  calc
    qFactor (j + 1) *
        (qPochhammerInv j * qFactorInv (j + 1) (by omega)) =
      qPochhammerInv j *
        (qFactorInv (j + 1) (by omega) * qFactor (j + 1)) := by ring
    _ = qPochhammerInv j := by rw [qFactorInv_mul_qFactor]; simp

theorem coeffNonneg_geometricSeries : CoeffNonneg geometricSeries := by
  intro k
  simp [geometricSeries]

theorem coeffNonneg_qFactorInv (r : ℕ) (hr : r ≠ 0) :
    CoeffNonneg (qFactorInv r hr) := by
  intro k
  unfold qFactorInv
  rw [PowerSeries.coeff_expand]
  split_ifs with h
  · exact coeffNonneg_geometricSeries _
  · simp

theorem coeffNonneg_qPochhammerInv (j : ℕ) :
    CoeffNonneg (qPochhammerInv j) := by
  unfold qPochhammerInv
  induction (Finset.range j) using Finset.induction_on with
  | empty =>
      intro k
      simp only [prod_empty, coeff_one]
      split <;> simp
  | @insert r s hrs ih =>
      rw [Finset.prod_insert hrs]
      exact (coeffNonneg_qFactorInv (r + 1) (by omega)).mul ih

/-- Exponent `j²+(t-1)j` in (2.2). -/
def hyperExponent (t j : ℕ) : ℕ := j ^ 2 + (t - 1) * j

/-- The `j`th summand in (2.2). -/
noncomputable def hyperTerm (t j : ℕ) : ℤ⟦X⟧ :=
  X ^ hyperExponent t j * qPochhammerInv j

@[simp] theorem hyperTerm_zero (t : ℕ) : hyperTerm t 0 = 1 := by
  simp [hyperTerm, hyperExponent, qPochhammerInv]

theorem coeffNonneg_hyperTerm (t j : ℕ) : CoeffNonneg (hyperTerm t j) :=
  (coeffNonneg_X_pow _).mul (coeffNonneg_qPochhammerInv j)

/-- Coefficientwise finite construction of the hypergeometric `R_t` in (2.2).
The intended interface is `t ≥ 1`. -/
noncomputable def hyperSeries (t : ℕ) : ℤ⟦X⟧ :=
  PowerSeries.mk fun k ↦
    ∑ j ∈ Finset.range (k + 1), coeff k (hyperTerm t j)

@[simp] theorem coeff_hyperSeries (t k : ℕ) :
    coeff k (hyperSeries t) =
      ∑ j ∈ Finset.range (k + 1), coeff k (hyperTerm t j) := by
  simp [hyperSeries]

theorem coeffNonneg_hyperSeries (t : ℕ) : CoeffNonneg (hyperSeries t) := by
  intro k
  rw [coeff_hyperSeries]
  exact Finset.sum_nonneg fun j hj ↦ coeffNonneg_hyperTerm t j k

/-- For positive `t`, a summand whose index exceeds the requested degree has
zero coefficient.  This is the finiteness fact behind `hyperSeries`. -/
theorem coeff_hyperTerm_eq_zero_of_lt_index {t j k : ℕ}
    (hkj : k < j) : coeff k (hyperTerm t j) = 0 := by
  unfold hyperTerm
  apply coeff_X_pow_mul_eq_zero_of_lt
  have hj_le_sq : j ≤ j ^ 2 := by nlinarith
  unfold hyperExponent
  omega

/-- The algebraic cancellation used when subtracting consecutive `R_t`
summands. -/
theorem hyperTerm_sub_succ (t j : ℕ) (ht : 0 < t) :
    hyperTerm t (j + 1) - hyperTerm (t + 1) (j + 1) =
      X ^ t * hyperTerm (t + 2) j := by
  have hexponent_succ :
    hyperExponent (t + 1) (j + 1) = hyperExponent t (j + 1) + (j + 1) := by
    unfold hyperExponent
    rw [Nat.add_sub_cancel]
    have ht_decomp : t - 1 + 1 = t := Nat.sub_add_cancel (by omega : 1 ≤ t)
    nlinarith
  have hexponent_shift :
      hyperExponent t (j + 1) = t + hyperExponent (t + 2) j := by
    unfold hyperExponent
    rw [show t + 2 - 1 = t + 1 by omega]
    have ht_decomp : t - 1 + 1 = t := Nat.sub_add_cancel (by omega : 1 ≤ t)
    nlinarith
  unfold hyperTerm
  rw [hexponent_succ, pow_add, hexponent_shift, pow_add]
  rw [show X ^ t * X ^ hyperExponent (t + 2) j * qPochhammerInv (j + 1) -
      X ^ t * X ^ hyperExponent (t + 2) j * X ^ (j + 1) *
        qPochhammerInv (j + 1) =
      X ^ t * X ^ hyperExponent (t + 2) j *
        (qFactor (j + 1) * qPochhammerInv (j + 1)) by
      simp only [qFactor]; ring]
  rw [qFactor_mul_qPochhammerInv_succ]
  ring

/-- The coefficient definition may be extended to any longer finite cutoff. -/
theorem coeff_hyperSeries_eq_sum_range (t k N : ℕ) (hkN : k < N) :
    coeff k (hyperSeries t) = ∑ j ∈ Finset.range N, coeff k (hyperTerm t j) := by
  rw [coeff_hyperSeries]
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hk : k = N
      · subst N
        rfl
      · have hklt : k < N := by omega
        conv_rhs => rw [Finset.sum_range_succ]
        rw [← ih hklt]
        rw [coeff_hyperTerm_eq_zero_of_lt_index (by omega : k < N), add_zero]

/-- The coefficientwise hypergeometric construction satisfies (3.1) at every
positive index. -/
theorem hyperSeries_recurrence (t : ℕ) (ht : 0 < t) :
    hyperSeries t = hyperSeries (t + 1) + X ^ t * hyperSeries (t + 2) := by
  ext k
  rw [map_add, coeff_X_pow_mul']
  by_cases htk : t ≤ k
  · rw [if_pos htk]
    rw [coeff_hyperSeries, coeff_hyperSeries]
    rw [coeff_hyperSeries_eq_sum_range (t + 2) (k - t) k (by omega)]
    conv_lhs => rw [Finset.sum_range_succ']
    conv_rhs =>
      lhs
      rw [Finset.sum_range_succ']
    simp only [hyperTerm_zero]
    have hterm (j : ℕ) :
        coeff k (hyperTerm t (j + 1)) =
          coeff k (hyperTerm (t + 1) (j + 1)) +
            coeff (k - t) (hyperTerm (t + 2) j) := by
      have h := congrArg (fun f : ℤ⟦X⟧ ↦ coeff k f) (hyperTerm_sub_succ t j ht)
      rw [map_sub, coeff_X_pow_mul', if_pos htk] at h
      linarith
    simp_rw [hterm]
    rw [Finset.sum_add_distrib]
    ring
  · rw [if_neg htk, add_zero]
    rw [coeff_hyperSeries, coeff_hyperSeries]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp
    · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have htlarge : k < t := Nat.lt_of_not_ge htk
      have hmul : t - 1 ≤ (t - 1) * j := by
        simpa using Nat.mul_le_mul_left (t - 1) hjpos
      have hkprod : k ≤ (t - 1) * j := by omega
      have hsq : 0 < j ^ 2 := by positivity
      have hexp : k < hyperExponent t j := by
        unfold hyperExponent
        omega
      have hmul' : t ≤ t * j := by
        simpa using Nat.mul_le_mul_left t hjpos
      have hexp' : k < hyperExponent (t + 1) j := by
        unfold hyperExponent
        rw [Nat.add_sub_cancel]
        omega
      unfold hyperTerm
      rw [coeff_X_pow_mul_eq_zero_of_lt _ hexp]
      rw [coeff_X_pow_mul_eq_zero_of_lt _ hexp']

theorem coeff_zero_hyperSeries (t : ℕ) : coeff 0 (hyperSeries t) = 1 := by
  rw [coeff_hyperSeries]
  simp

theorem coeff_hyperSeries_eq_zero_of_pos_lt {t k : ℕ} (hk : 0 < k) (hkt : k < t) :
    coeff k (hyperSeries t) = 0 := by
  rw [coeff_hyperSeries]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    simp [hk.ne']
  · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
    have hmul : t - 1 ≤ (t - 1) * j := by
      simpa using Nat.mul_le_mul_left (t - 1) hjpos
    have hkprod : k ≤ (t - 1) * j := by omega
    have hsq : 0 < j ^ 2 := by positivity
    unfold hyperTerm
    apply coeff_X_pow_mul_eq_zero_of_lt
    unfold hyperExponent
    omega

end Borwein
