import Borwein.Hypergeometric
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false

namespace Borwein.FormalSeriesValue
noncomputable section
open PowerSeries Complex

def term (f : ℤ⟦X⟧) (q : ℂ) (k : ℕ) : ℂ := ((coeff k f:ℤ):ℂ)*q^k

def Converges (f : ℤ⟦X⟧) (q z : ℂ) : Prop :=
  Summable (fun k : ℕ => ‖term f q k‖) ∧ HasSum (term f q) z

theorem term_mul (f g : ℤ⟦X⟧) (q : ℂ) (n : ℕ) :
    term (f*g) q n=∑ p ∈ Finset.antidiagonal n, term f q p.1*term g q p.2 := by
  unfold term
  rw [coeff_mul, Int.cast_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hn := Finset.mem_antidiagonal.mp hp
  rw [Int.cast_mul, ← hn, pow_add]
  ring

theorem converges_mul {f g : ℤ⟦X⟧} {q z w : ℂ}
    (hf : Converges f q z) (hg : Converges g q w) : Converges (f*g) q (z*w) := by
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hf.1 hg.1
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf.1 hg.1
  simp_rw [← term_mul] at hs he
  refine ⟨hs, ?_⟩
  rw [hf.2.tsum_eq, hg.2.tsum_eq] at he
  rw [he]
  exact hs.of_norm.hasSum

theorem converges_X_pow (q : ℂ) (e : ℕ) : Converges ((X:ℤ⟦X⟧)^e) q (q^e) := by
  have he : term ((X:ℤ⟦X⟧)^e) q=(fun k : ℕ => if k=e then q^e else 0) := by
    funext k
    by_cases hk : k=e
    · subst k; simp [term]
    · simp [term, coeff_X_pow, hk, Ne.symm hk]
  unfold Converges
  rw [he]
  constructor
  · simpa only [apply_ite, norm_zero] using (hasSum_ite_eq e ‖q^e‖).summable
  · exact hasSum_ite_eq e (q^e)

theorem converges_one (q : ℂ) : Converges (1:ℤ⟦X⟧) q 1 := by
  simpa only [pow_zero] using converges_X_pow q 0

theorem nonneg_norm (f : ℤ⟦X⟧) (hf : CoeffNonneg f) (q : ℂ) (k : ℕ) :
    ‖term f q k‖=(term f (‖q‖:ℂ) k).re := by
  unfold term
  have hc : 0 ≤ ((coeff k f:ℤ):ℝ) := by exact_mod_cast hf k
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hc, Complex.norm_pow]
  simp [← Complex.ofReal_pow]

theorem converges_qFactorInv (q : ℂ) (hq : ‖q‖ < 1) (r : ℕ) (hr : r ≠ 0) :
    Converges (qFactorInv r hr) q ((1-q^r)⁻¹) := by
  have he (k : ℕ) : term (qFactorInv r hr) q k=if r ∣ k then q^k else 0 := by
    simp [term, qFactorInv, coeff_expand, geometricSeries]
  have hi : Function.Injective (fun k : ℕ => r*k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) hab
  constructor
  · apply (summable_geometric_of_lt_one (norm_nonneg q) hq).of_nonneg_of_le
      (fun k => norm_nonneg _) (fun k => ?_)
    rw [he]
    split_ifs <;> simp [Complex.norm_pow, pow_nonneg (norm_nonneg q)]
  · apply (hi.hasSum_iff (f := term (qFactorInv r hr) q) (by
      intro k hk
      rw [he, if_neg]
      rintro ⟨l,hl⟩
      exact hk ⟨l,hl.symm⟩)).mp
    have hqr : ‖q^r‖ < 1 := by
      rw [Complex.norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq hr
    apply (hasSum_geometric_of_norm_lt_one hqr).congr_fun
    intro k
    simp only [Function.comp_def, he, dvd_mul_right, if_true, pow_mul]

end
end Borwein.FormalSeriesValue
