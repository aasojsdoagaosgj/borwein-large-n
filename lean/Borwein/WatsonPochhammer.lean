import Borwein.EulerFiniteTriple

set_option autoImplicit false

namespace Borwein.WatsonPochhammer
noncomputable section
open Complex EndpointEulerTail EulerQBinomial EulerFiniteBinomial EulerFiniteTriple

def paired (q a : ℂ) (n : ℕ) : ℂ := finiteEuler n q*product q (-a) n
def inverse (q a : ℂ) (k : ℤ) : ℂ := if 0 ≤ k then (paired q a k.toNat)⁻¹ else 0

theorem product_ne_zero (q a : ℂ) (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) (n : ℕ) :
    product q (-a) n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  simpa only [neg_mul, sub_eq_add_neg] using hA j

theorem paired_ne_zero (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) (n : ℕ) : paired q a n ≠ 0 :=
  mul_ne_zero (finiteEuler_ne_zero n q hq) (product_ne_zero q a hA n)

theorem paired_succ (q a : ℂ) (n : ℕ) :
    paired q a (n+1)=paired q a n*((1-q^(n+1))*(1-a*q^n)) := by
  unfold paired
  rw [pochhammer_succ, product_append]
  ring

theorem inverse_negative (q a : ℂ) (k : ℤ) (hk : k < 0) : inverse q a k=0 := by
  simp only [inverse, if_neg (not_le.mpr hk)]

theorem inverse_nat (q a : ℂ) (n : ℕ) : inverse q a (n:ℤ)=(paired q a n)⁻¹ := by
  simp [inverse]

theorem inverse_zero (q a : ℂ) : inverse q a 0=1 := by
  simp [inverse, paired, finiteEuler, product]

/-- The inverse recurrence remains valid at and outside the finite-support boundary. -/
theorem inverse_step (q a : ℂ) (hq : ‖q‖ < 1)
    (hA : ∀ j : ℕ, 1-a*q^j ≠ 0) (k : ℤ) :
    inverse q a (k-1)=(1-q^k)*(1-a*q^(k-1))*inverse q a k := by
  by_cases hk : k < 0
  · rw [inverse_negative q a (k-1) (by omega), inverse_negative q a k hk, mul_zero]
  by_cases hk0 : k=0
  · subst k
    rw [inverse_negative q a (0-1) (by omega)]
    simp
  obtain ⟨j,hj⟩ : ∃ j : ℕ, k=(j+1:ℕ) := ⟨(k-1).toNat, by omega⟩
  subst k
  rw [show ((j+1:ℕ):ℤ)-1=(j:ℤ) by omega, inverse_nat, inverse_nat,
    zpow_natCast, zpow_natCast, paired_succ]
  have hqj : 1-q^(j+1) ≠ 0 := factor_ne_zero q hq _ (by omega)
  field_simp [paired_ne_zero q a hq hA j, hA j, hqj]

end
end Borwein.WatsonPochhammer
