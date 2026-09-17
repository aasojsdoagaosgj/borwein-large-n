import Borwein.EndpointTailLog

set_option autoImplicit false

namespace Borwein.PeriodicFactorLoss
noncomputable section
open Complex

def lossTerm (z : ℂ) (k : ℕ) : ℝ := (‖z‖^k-(z^k).re)/(k:ℝ)

theorem real_quotient (z : ℂ) (k : ℕ) : (z/(k:ℂ)).re=z.re/(k:ℝ) := by
  simpa only [Complex.ofReal_natCast] using Complex.div_ofReal_re z (k:ℝ)

theorem lossTerm_nonneg (z : ℂ) (k : ℕ) : 0 ≤ lossTerm z k := by
  have h : (z^k).re ≤ ‖z‖^k := by simpa only [Complex.norm_pow] using re_le_norm (z^k)
  exact div_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg k)

theorem loss_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (lossTerm z) ((log (1-z)).re-(log (1-(‖z‖:ℂ))).re) := by
  have hr : ‖(‖z‖:ℂ)‖ < 1 := by simpa using hz
  have hs := (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hr)).sub
    (Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hz))
  have he : (-log (1-(‖z‖:ℂ))).re-(-log (1-z)).re =
      (log (1-z)).re-(log (1-(‖z‖:ℂ))).re := by simp only [Complex.neg_re]; ring
  rw [he] at hs
  apply hs.congr_fun
  intro k
  rw [real_quotient, real_quotient]
  simp only [lossTerm, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- The first Fourier frequency gives a lower bound for the logarithmic norm loss. -/
theorem first_frequency_loss (z : ℂ) (hz : ‖z‖ < 1) :
    ‖z‖-z.re ≤ (log (1-z)).re-(log (1-(‖z‖:ℂ))).re := by
  have hs := loss_hasSum z hz
  have h := Summable.sum_le_tsum ({1}:Finset ℕ) (fun k _ => lossTerm_nonneg z k) hs.summable
  rw [hs.tsum_eq] at h
  simpa [lossTerm] using h

end
end Borwein.PeriodicFactorLoss
