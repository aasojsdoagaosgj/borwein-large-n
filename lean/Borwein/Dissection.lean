import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.Tactic

/-!
# The residue-class consequence of the Borwein five-dissection

The classical five-dissection itself is deliberately not assumed as an axiom.
This file isolates and proves the formal implication used in (2.4): every
series having the displayed three-term shape has zero coefficients in residue
classes three and four modulo five.
-/

namespace Borwein

open PowerSeries

private lemma five_ne_zero : (5 : ℕ) ≠ 0 := by norm_num

/-- A generic series with terms in residue classes `0`, `1`, and `2` modulo five. -/
noncomputable def residueForm (A B C : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  expand 5 five_ne_zero A - X ^ 1 * expand 5 five_ne_zero B -
    X ^ 2 * expand 5 five_ne_zero C

private theorem coeff_residueForm_zero (A B C : ℤ⟦X⟧) (m : ℕ)
    (hm2 : 2 ≤ m) (h0 : ¬5 ∣ m) (h1 : ¬5 ∣ m - 1) (h2 : ¬5 ∣ m - 2) :
    coeff m (residueForm A B C) = 0 := by
  simp only [residueForm, map_sub, coeff_X_pow_mul']
  rw [if_pos (by omega : 1 ≤ m), if_pos hm2]
  rw [coeff_expand_of_not_dvd 5 five_ne_zero A h0]
  rw [coeff_expand_of_not_dvd 5 five_ne_zero B h1]
  rw [coeff_expand_of_not_dvd 5 five_ne_zero C h2]
  ring

/-- Equation (2.4), residue class three, from the shape of (2.3). -/
theorem coeff_residueForm_five_mul_add_three (A B C : ℤ⟦X⟧) (j : ℕ) :
    coeff (5 * j + 3) (residueForm A B C) = 0 := by
  apply coeff_residueForm_zero A B C
  · omega
  · omega
  · omega
  · omega

/-- Equation (2.4), residue class four, from the shape of (2.3). -/
theorem coeff_residueForm_five_mul_add_four (A B C : ℤ⟦X⟧) (j : ℕ) :
    coeff (5 * j + 4) (residueForm A B C) = 0 := by
  apply coeff_residueForm_zero A B C
  · omega
  · omega
  · omega
  · omega

/-- The precise right-hand side of (2.3), with arbitrary input series `g,h`. -/
noncomputable def fiveDissectionRhs (g h : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  residueForm (g ^ 2) (g * h) (h ^ 2)

theorem coeff_fiveDissectionRhs_mod_three (g h : ℤ⟦X⟧) (j : ℕ) :
    coeff (5 * j + 3) (fiveDissectionRhs g h) = 0 :=
  coeff_residueForm_five_mul_add_three _ _ _ _

theorem coeff_fiveDissectionRhs_mod_four (g h : ℤ⟦X⟧) (j : ℕ) :
    coeff (5 * j + 4) (fiveDissectionRhs g h) = 0 :=
  coeff_residueForm_five_mul_add_four _ _ _ _

/-- Safe interface for importing a separately proved classical five-dissection. -/
theorem five_dissection_implies_zero_classes (G g h : ℤ⟦X⟧)
    (hdissection : G = fiveDissectionRhs g h) (j : ℕ) :
    coeff (5 * j + 3) G = 0 ∧ coeff (5 * j + 4) G = 0 := by
  subst G
  exact ⟨coeff_fiveDissectionRhs_mod_three g h j,
    coeff_fiveDissectionRhs_mod_four g h j⟩

end Borwein
