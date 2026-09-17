import Mathlib.Tactic

/-!
# Algebraic core of the nonnegative-kernel recurrence

This file proves equation (3.2) from three instances of (3.1), in an arbitrary
commutative ring.  Positivity and the infinite iteration in (3.3) are separate
tasks and are not claimed here.
-/

namespace Borwein

open scoped BigOperators

/-- Abstract form of the Rogers--Ramanujan recurrence (3.1). -/
def RRRecurrence {A : Type*} [CommRing A] (Q : A) (R : ℕ → A) : Prop :=
  ∀ t, R t = R (t + 1) + Q ^ t * R (t + 2)

/-- The numerator called `W_t` in the manuscript. -/
def kernel {A : Type*} [CommRing A] (Q : A) (R : ℕ → A) (t : ℕ) : A :=
  R (t + 1) ^ 2 - Q * R t * R (t + 2)

/-- The one-step identity (3.2), independent of coefficient estimates. -/
theorem kernel_step {A : Type*} [CommRing A] (Q : A) (R : ℕ → A)
    (hR : RRRecurrence Q R) (t : ℕ) :
    kernel Q R t =
      (1 - Q) * R (t + 1) * R (t + 2) + Q ^ (2 * t + 2) * kernel Q R (t + 2) := by
  have h0 := hR t
  have h1 := hR (t + 1)
  have h2 := hR (t + 2)
  simp only [Nat.add_assoc] at h1 h2
  norm_num at h1 h2
  rw [show 2 * t + 2 = (t + 1) + (t + 1) by omega, pow_add]
  simp only [kernel]
  rw [h0, h1, h2]
  simp only [pow_succ]
  ring

/-- The exact finite telescoping identity behind (3.3).  The final term is the
remainder that must be sent coefficientwise to arbitrarily high order before
the manuscript's infinite-series formula is obtained. -/
theorem kernel_iterate {A : Type*} [CommRing A] (Q : A) (R : ℕ → A)
    (hR : RRRecurrence Q R) (t N : ℕ) :
    kernel Q R t =
      (1 - Q) * ∑ j ∈ Finset.range N,
        Q ^ (2 * j * (t + j)) * R (t + 2 * j + 1) * R (t + 2 * j + 2) +
      Q ^ (2 * N * (t + N)) * kernel Q R (t + 2 * N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, kernel_step Q R hR (t + 2 * N), Finset.sum_range_succ]
      have hexponent :
          2 * (N + 1) * (t + (N + 1)) =
            2 * N * (t + N) + (2 * (t + 2 * N) + 2) := by
        ring_nf
      rw [hexponent, pow_add]
      ring_nf
      simp only [Nat.add_assoc, Nat.add_comm, Nat.mul_assoc, Nat.mul_comm]

end Borwein
