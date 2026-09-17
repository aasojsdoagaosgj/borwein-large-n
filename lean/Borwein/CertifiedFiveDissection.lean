import Borwein.StableOuterCoefficient
import Borwein.StableMiddleCoefficient
import Borwein.CertifiedLowWeakZero

set_option autoImplicit false

namespace Borwein.CertifiedFiveDissection
noncomputable section
open PowerSeries StableBorweinSeries

theorem shifted_coefficient (f : ℤ⟦X⟧) (a b j : ℕ) (ha : a < 5) (hb : b < 5) :
    coeff (5*j+b) (X^a*expand 5 (by omega) f)=if b=a then coeff j f else 0 := by
  rw [coeff_X_pow_mul']
  by_cases hba : b=a
  · subst b
    rw [if_pos (by omega), show 5*j+a-a=5*j by omega, coeff_expand]
    simp
  · rw [if_neg hba]
    by_cases hle : a ≤ 5*j+b
    · rw [if_pos hle, coeff_expand_of_not_dvd 5 (by omega) f (by omega)]
    · rw [if_neg hle]

theorem residue_coefficient (A B C : ℤ⟦X⟧) (b j : ℕ) (hb : b < 5) :
    coeff (5*j+b) (residueForm A B C)=
      (if b=0 then coeff j A else 0)-(if b=1 then coeff j B else 0)-
        (if b=2 then coeff j C else 0) := by
  have h0 := shifted_coefficient A 0 b j (by omega) hb
  simp only [pow_zero, one_mul] at h0
  unfold residueForm
  rw [map_sub, map_sub, h0, shifted_coefficient B 1 b j (by omega) hb,
    shifted_coefficient C 2 b j (by omega) hb]

/-- The classical five-dissection for the actual stable Borwein coefficients. -/
theorem five_dissection : series=fiveDissectionRhs (rrSeries 1) (rrSeries 2) := by
  apply PowerSeries.ext
  intro m
  rw [coeff_series]
  obtain ⟨j,b,hb,hm⟩ : ∃ j b : ℕ, b < 5 ∧ m=5*j+b :=
    ⟨m/5,m%5,Nat.mod_lt _ (by omega),by omega⟩
  rw [hm, fiveDissectionRhs, residue_coefficient _ _ _ b j hb]
  interval_cases b
  · simpa using StableOuterCoefficient.stable_class_zero j
  · simpa using StableMiddleCoefficient.stable_class_one j
  · simpa using StableOuterCoefficient.stable_class_two j
  · simpa using CertifiedLowWeakZero.stable_weak_zero (5*j+3) (by omega)
  · simpa using CertifiedLowWeakZero.stable_weak_zero (5*j+4) (by omega)

end
end Borwein.CertifiedFiveDissection
