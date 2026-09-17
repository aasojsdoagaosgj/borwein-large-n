import Borwein.FormalSeriesValue
import Borwein.Dissection

set_option autoImplicit false

namespace Borwein.FormalSeriesOperations
noncomputable section
open Complex PowerSeries FormalSeriesValue

theorem term_sub (f g : ℤ⟦X⟧) (q : ℂ) (k : ℕ) :
    term (f-g) q k=term f q k-term g q k := by
  simp only [term, map_sub, Int.cast_sub, sub_mul]

theorem converges_sub {f g : ℤ⟦X⟧} {q z w : ℂ}
    (hf : Converges f q z) (hg : Converges g q w) : Converges (f-g) q (z-w) := by
  refine ⟨?_, ?_⟩
  · apply (hf.1.add hg.1).of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    rw [term_sub]
    exact norm_sub_le _ _
  · exact (hf.2.sub hg.2).congr_fun (fun k => term_sub f g q k)

theorem converges_pow {f : ℤ⟦X⟧} {q z : ℂ} (hf : Converges f q z) (n : ℕ) :
    Converges (f^n) q (z^n) := by
  induction n with
  | zero => simpa using converges_one q
  | succ n ih => simpa only [pow_succ] using converges_mul ih hf

theorem expanded_term (f : ℤ⟦X⟧) (q : ℂ) (r : ℕ) (hr : r ≠ 0) (k : ℕ) :
    term (expand r hr f) q (r*k)=term f (q^r) k := by
  simp [term, coeff_expand, hr, pow_mul]

theorem expanded_term_outside (f : ℤ⟦X⟧) (q : ℂ) (r : ℕ) (hr : r ≠ 0)
    (k : ℕ) (hk : k ∉ Set.range (fun j : ℕ => r*j)) : term (expand r hr f) q k=0 := by
  have hd : ¬ r ∣ k := by
    rintro ⟨j,hj⟩
    exact hk ⟨j,hj.symm⟩
  simp only [term, coeff_expand_of_not_dvd r hr f hd, Int.cast_zero, zero_mul]

theorem converges_expand {f : ℤ⟦X⟧} {q z : ℂ} (r : ℕ) (hr : r ≠ 0)
    (hf : Converges f (q^r) z) : Converges (expand r hr f) q z := by
  have hi : Function.Injective (fun k : ℕ => r*k) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hr) hab
  constructor
  · have hs := (hi.hasSum_iff (f := fun k => ‖term (expand r hr f) q k‖)
      (fun k hk => by rw [expanded_term_outside f q r hr k hk, norm_zero])).mp
      (hf.1.hasSum.congr_fun (fun k => by
        change ‖term (expand r hr f) q (r*k)‖=‖term f (q^r) k‖
        rw [expanded_term]))
    exact hs.summable
  · exact (hi.hasSum_iff (f := term (expand r hr f) q)
      (expanded_term_outside f q r hr)).mp
      (hf.2.congr_fun (fun k => expanded_term f q r hr k))

theorem converges_fiveDissectionRhs (g h : ℤ⟦X⟧) (q z w : ℂ)
    (hg : Converges g (q^5) z) (hh : Converges h (q^5) w) :
    Converges (fiveDissectionRhs g h) q (z^2-q*(z*w)-q^2*w^2) := by
  have h1 := converges_expand 5 (by omega) (converges_pow hg 2)
  have h2 := converges_mul (converges_X_pow q 1)
    (converges_expand 5 (by omega) (converges_mul hg hh))
  have h3 := converges_mul (converges_X_pow q 2)
    (converges_expand 5 (by omega) (converges_pow hh 2))
  simpa only [fiveDissectionRhs, residueForm, pow_one] using converges_sub (converges_sub h1 h2) h3

end
end Borwein.FormalSeriesOperations
