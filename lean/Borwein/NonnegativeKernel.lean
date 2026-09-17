import Borwein.Kernel
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-!
# Coefficientwise finite form of the nonnegative-kernel expansion

This file specializes the finite telescoping identity in `Borwein.Kernel` to
formal power series over the integers.  It proves two facts needed before the
infinite formula (3.3) can safely be used:

* below an explicit degree, the shifted remainder has zero coefficient;
* if all `R_t` have nonnegative coefficients, every coefficient of the finite
  sum on the right is nonnegative.

No topology or unjustified passage to an infinite sum is used.
-/

namespace Borwein

open scoped BigOperators
open Finset PowerSeries

/-- Coefficientwise nonnegativity for an integer formal power series. -/
def CoeffNonneg (f : ℤ⟦X⟧) : Prop := ∀ k, 0 ≤ coeff k f

lemma coeffNonneg_zero : CoeffNonneg (0 : ℤ⟦X⟧) := by
  intro k
  simp

lemma coeffNonneg_X_pow (e : ℕ) : CoeffNonneg ((X : ℤ⟦X⟧) ^ e) := by
  intro k
  rw [coeff_X_pow]
  split <;> simp

lemma CoeffNonneg.add {f g : ℤ⟦X⟧} (hf : CoeffNonneg f) (hg : CoeffNonneg g) :
    CoeffNonneg (f + g) := by
  intro k
  simpa only [map_add] using add_nonneg (hf k) (hg k)

lemma CoeffNonneg.mul {f g : ℤ⟦X⟧} (hf : CoeffNonneg f) (hg : CoeffNonneg g) :
    CoeffNonneg (f * g) := by
  intro k
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ ↦ mul_nonneg (hf p.1) (hg p.2)

lemma coeffNonneg_sum {ι : Type*} {s : Finset ι} {f : ι → ℤ⟦X⟧}
    (hf : ∀ i ∈ s, CoeffNonneg (f i)) : CoeffNonneg (∑ i ∈ s, f i) := by
  intro k
  simp only [map_sum]
  exact Finset.sum_nonneg fun i hi ↦ hf i hi k

/-- The finite sum occurring in the exact `N`-step version of (3.3). -/
noncomputable def kernelPartialSum (R : ℕ → ℤ⟦X⟧) (t N : ℕ) : ℤ⟦X⟧ :=
  ∑ j ∈ Finset.range N,
    X ^ (2 * j * (t + j)) * R (t + 2 * j + 1) * R (t + 2 * j + 2)

/-- Nonnegative input series make every finite approximant nonnegative. -/
theorem coeffNonneg_kernelPartialSum (R : ℕ → ℤ⟦X⟧)
    (hRnonneg : ∀ s, CoeffNonneg (R s)) (t N : ℕ) :
    CoeffNonneg (kernelPartialSum R t N) := by
  unfold kernelPartialSum
  apply coeffNonneg_sum
  intro j hj
  exact ((coeffNonneg_X_pow _).mul (hRnonneg _)).mul (hRnonneg _)

/-- A power of `X` contributes no coefficient below its shift. -/
lemma coeff_X_pow_mul_eq_zero_of_lt (f : ℤ⟦X⟧) {e k : ℕ} (hk : k < e) :
    coeff k (X ^ e * f) = 0 := by
  rw [coeff_X_pow_mul']
  simp [Nat.not_le.mpr hk]

/-- Coefficientwise finite form of (3.3): beneath the displayed cutoff, the
remainder in `kernel_iterate` vanishes exactly. -/
theorem coeff_kernel_eq_finite_expansion (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R) (t N k : ℕ)
    (hk : k < 2 * N * (t + N)) :
    coeff k (kernel X R t) =
      coeff k ((1 - X) * kernelPartialSum R t N) := by
  have hiterate := kernel_iterate (X : ℤ⟦X⟧) R hR t N
  have hcoeff := congrArg (fun f : ℤ⟦X⟧ ↦ coeff k f) hiterate
  rw [map_add] at hcoeff
  have htail :
      coeff k (X ^ (2 * N * (t + N)) * kernel X R (t + 2 * N)) = 0 :=
    coeff_X_pow_mul_eq_zero_of_lt _ hk
  rw [htail, add_zero] at hcoeff
  simpa only [kernelPartialSum] using hcoeff

/-- For every requested coefficient there is a concrete finite stage at which
the remainder vanishes. -/
theorem exists_finite_kernel_expansion (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R) (t k : ℕ) :
    ∃ N, coeff k (kernel X R t) =
      coeff k ((1 - X) * kernelPartialSum R t N) := by
  refine ⟨k + 1, coeff_kernel_eq_finite_expansion R hR t (k + 1) k ?_⟩
  nlinarith [Nat.zero_le t]

/-- The geometric series `1 + X + X² + ⋯`, used as the formal inverse of
`1-X`. -/
noncomputable def geometricSeries : ℤ⟦X⟧ := PowerSeries.mk 1

lemma geometricSeries_mul_one_sub_X : geometricSeries * (1 - X) = (1 : ℤ⟦X⟧) := by
  unfold geometricSeries
  exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ

/-- The formal quotient `W_t / (1-X)`.  This definition uses the explicit
geometric-series inverse, so no field of fractions is involved. -/
noncomputable def kernelQuotient (R : ℕ → ℤ⟦X⟧) (t : ℕ) : ℤ⟦X⟧ :=
  geometricSeries * kernel X R t

/-- `kernelQuotient` really is a quotient by `1-X`. -/
theorem one_sub_X_mul_kernelQuotient (R : ℕ → ℤ⟦X⟧) (t : ℕ) :
    (1 - X) * kernelQuotient R t = kernel X R t := by
  unfold kernelQuotient
  calc
    (1 - X) * (geometricSeries * kernel X R t) =
        (geometricSeries * (1 - X)) * kernel X R t := by ring
    _ = kernel X R t := by rw [geometricSeries_mul_one_sub_X]; simp

/-- Uniqueness of the formal quotient by `1-X`. -/
theorem kernelQuotient_unique (R : ℕ → ℤ⟦X⟧) (t : ℕ) (D : ℤ⟦X⟧)
    (hD : (1 - X) * D = kernel X R t) : D = kernelQuotient R t := by
  calc
    D = 1 * D := by simp
    _ = (geometricSeries * (1 - X)) * D := by rw [geometricSeries_mul_one_sub_X]
    _ = geometricSeries * ((1 - X) * D) := by ring
    _ = geometricSeries * kernel X R t := by rw [hD]
    _ = kernelQuotient R t := rfl

/-- The coefficient of the formal quotient is already equal to the coefficient
of the concrete `(k+1)`-stage finite sum. -/
theorem coeff_kernelQuotient_eq_partial (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R) (t k : ℕ) :
    coeff k (kernelQuotient R t) = coeff k (kernelPartialSum R t (k + 1)) := by
  have hkcutoff : k < 2 * (k + 1) * (t + (k + 1)) := by
    nlinarith [Nat.zero_le t]
  unfold kernelQuotient
  rw [coeff_mul]
  calc
    ∑ p ∈ antidiagonal k, coeff p.1 geometricSeries * coeff p.2 (kernel X R t) =
        ∑ p ∈ antidiagonal k, coeff p.1 geometricSeries *
          coeff p.2 ((1 - X) * kernelPartialSum R t (k + 1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp_le : p.2 ≤ k := by
        have hp_sum := mem_antidiagonal.mp hp
        omega
      rw [coeff_kernel_eq_finite_expansion R hR t (k + 1) p.2
        (lt_of_le_of_lt hp_le hkcutoff)]
    _ = coeff k (geometricSeries * ((1 - X) * kernelPartialSum R t (k + 1))) := by
      rw [coeff_mul]
    _ = coeff k (kernelPartialSum R t (k + 1)) := by
      rw [← mul_assoc, geometricSeries_mul_one_sub_X, one_mul]

/-- The formal quotient has nonnegative integer coefficients whenever the
input Rogers--Ramanujan series do. -/
theorem coeffNonneg_kernelQuotient (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hRnonneg : ∀ s, CoeffNonneg (R s)) (t : ℕ) :
    CoeffNonneg (kernelQuotient R t) := by
  intro k
  rw [coeff_kernelQuotient_eq_partial R hR t k]
  exact coeffNonneg_kernelPartialSum R hRnonneg t (k + 1) k

/-- The series on the right of (3.4), corresponding to `t=1`. -/
noncomputable def nonnegativeKernelSeries (R : ℕ → ℤ⟦X⟧) : ℤ⟦X⟧ :=
  kernelQuotient R 1

theorem coeffNonneg_nonnegativeKernelSeries (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hRnonneg : ∀ s, CoeffNonneg (R s)) :
    CoeffNonneg (nonnegativeKernelSeries R) :=
  coeffNonneg_kernelQuotient R hR hRnonneg 1

/-- The coefficient sequence called `d_K` in (3.4). -/
noncomputable def dCoeff (R : ℕ → ℤ⟦X⟧) (K : ℕ) : ℤ :=
  coeff K (nonnegativeKernelSeries R)

theorem dCoeff_nonneg (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hRnonneg : ∀ s, CoeffNonneg (R s)) (K : ℕ) :
    0 ≤ dCoeff R K :=
  coeffNonneg_nonnegativeKernelSeries R hR hRnonneg K

/-- The `j=0` term gives a coefficientwise lower bound for `d_K`. -/
theorem baseProduct_coeff_le_dCoeff (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hRnonneg : ∀ s, CoeffNonneg (R s)) (K : ℕ) :
    coeff K (R 2 * R 3) ≤ dCoeff R K := by
  unfold dCoeff nonnegativeKernelSeries
  rw [coeff_kernelQuotient_eq_partial R hR 1 K]
  unfold kernelPartialSum
  simp only [map_sum]
  have hterms : ∀ j ∈ Finset.range (K + 1),
      0 ≤ coeff K (X ^ (2 * j * (1 + j)) * R (1 + 2 * j + 1) * R (1 + 2 * j + 2)) := by
    intro j hj
    exact (((coeffNonneg_X_pow _).mul (hRnonneg _)).mul (hRnonneg _)) K
  have hle := Finset.single_le_sum
    (s := Finset.range (K + 1))
    (f := fun j ↦ coeff K
      (X ^ (2 * j * (1 + j)) * R (1 + 2 * j + 1) * R (1 + 2 * j + 2)))
    hterms (by simp : 0 ∈ Finset.range (K + 1))
  simpa using hle

theorem dCoeff_pos_of_baseProduct_pos (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hRnonneg : ∀ s, CoeffNonneg (R s)) {K : ℕ}
    (hpositive : 0 < coeff K (R 2 * R 3)) :
    0 < dCoeff R K :=
  hpositive.trans_le (baseProduct_coeff_le_dCoeff R hR hRnonneg K)

/-- The constant coefficient `d₀=1`, separated from the later construction of
the concrete Rogers--Ramanujan series. -/
theorem coeff_zero_nonnegativeKernelSeries (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hconstant2 : coeff 0 (R 2) = 1) (hconstant3 : coeff 0 (R 3) = 1) :
    coeff 0 (nonnegativeKernelSeries R) = 1 := by
  unfold nonnegativeKernelSeries
  rw [coeff_kernelQuotient_eq_partial R hR 1 0]
  simp [kernelPartialSum, coeff_mul, hconstant2, hconstant3]

theorem dCoeff_zero (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hconstant2 : coeff 0 (R 2) = 1) (hconstant3 : coeff 0 (R 3) = 1) :
    dCoeff R 0 = 1 :=
  coeff_zero_nonnegativeKernelSeries R hR hconstant2 hconstant3

/-- The linear coefficient `d₁=0`, under exactly the two input coefficient
facts about `R₂` and `R₃` that are needed. -/
theorem coeff_one_nonnegativeKernelSeries (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hconstant2 : coeff 0 (R 2) = 1) (hconstant3 : coeff 0 (R 3) = 1)
    (hlinear2 : coeff 1 (R 2) = 0) (hlinear3 : coeff 1 (R 3) = 0) :
    coeff 1 (nonnegativeKernelSeries R) = 0 := by
  unfold nonnegativeKernelSeries
  rw [coeff_kernelQuotient_eq_partial R hR 1 1]
  have hpartial :
      kernelPartialSum R 1 2 = R 2 * R 3 + X ^ 4 * R 4 * R 5 := by
    norm_num [kernelPartialSum, Finset.sum_range_succ]
  rw [hpartial, map_add]
  have hshift : coeff 1 (X ^ 4 * R 4 * R 5) = 0 := by
    rw [mul_assoc]
    exact coeff_X_pow_mul_eq_zero_of_lt _ (by norm_num)
  rw [hshift, add_zero, PowerSeries.coeff_one_mul]
  simp only [← coeff_zero_eq_constantCoeff, hconstant2, hconstant3, hlinear2, hlinear3,
    mul_one, zero_add]

theorem dCoeff_one (R : ℕ → ℤ⟦X⟧)
    (hR : RRRecurrence (X : ℤ⟦X⟧) R)
    (hconstant2 : coeff 0 (R 2) = 1) (hconstant3 : coeff 0 (R 3) = 1)
    (hlinear2 : coeff 1 (R 2) = 0) (hlinear3 : coeff 1 (R 3) = 0) :
    dCoeff R 1 = 0 :=
  coeff_one_nonnegativeKernelSeries R hR hconstant2 hconstant3 hlinear2 hlinear3

end Borwein
