import Borwein.EndpointTailFourier

set_option autoImplicit false

namespace Borwein.InverseEulerLoss
noncomputable section
open Complex EndpointTailLog EndpointTailFourier

def geometricLoss (q : ℂ) : ℝ := ‖q‖/(1-‖q‖)-(q/(1-q)).re
def frequencyLoss (q : ℂ) (l : ℕ) : ℝ := geometricLoss (q^(l+1))/(l+1:ℝ)
def totalLoss (q : ℂ) : ℝ := (inverseLog 0 (‖q‖:ℂ)).re-(inverseLog 0 q).re

theorem geometricLoss_nonneg (q : ℂ) (hq : ‖q‖ < 1) :
    0 ≤ geometricLoss q := by
  have hd : 1-‖q‖ ≤ ‖1-q‖ := by simpa using norm_sub_norm_le (1:ℂ) q
  have he : (q/(1-q)).re ≤ ‖q‖/(1-‖q‖) := calc
    _ ≤ ‖q/(1-q)‖ := re_le_norm _
    _ = ‖q‖/‖1-q‖ := norm_div _ _
    _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg q) (by linarith) hd
  exact sub_nonneg.mpr he

theorem frequencyLoss_nonneg (q : ℂ) (hq : ‖q‖ < 1) (l : ℕ) :
    0 ≤ frequencyLoss q l := by
  have hp : ‖q^(l+1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  exact div_nonneg (geometricLoss_nonneg _ hp) (by positivity)

theorem frequency_real (q : ℂ) (l : ℕ) :
    (frequency 0 q l).re = (q^(l+1)/(1-q^(l+1))).re/(l+1:ℝ) := by
  have he : frequency 0 q l = (q^(l+1)/(1-q^(l+1)))/((l+1:ℕ):ℂ) := by
    simp only [frequency, zero_add, one_mul, div_div]
    rw [mul_comm]
  rw [he]
  simpa using
    Complex.div_ofReal_re (q^(l+1)/(1-q^(l+1))) ((l+1:ℕ):ℝ)

theorem loss_hasSum (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (frequencyLoss q) (totalLoss q) := by
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  have hs (z : ℂ) (hz : ‖z‖ < 1) : HasSum (frequency 0 z) (inverseLog 0 z) := by
    rw [inverseLog_series _ z hz]
    exact (frequency_summable 0 z hz).hasSum
  have he := (Complex.hasSum_re (hs _ hr)).sub (Complex.hasSum_re (hs q hq))
  apply he.congr_fun
  intro l
  rw [frequency_real, frequency_real]
  simp only [frequencyLoss, geometricLoss, norm_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
  ring

theorem finite_loss_le (q : ℂ) (hq : ‖q‖ < 1) (s : Finset ℕ) :
    ∑ l ∈ s, frequencyLoss q l ≤ totalLoss q := by
  have hs := loss_hasSum q hq
  have he := Summable.sum_le_tsum s (fun l _ => frequencyLoss_nonneg q hq l) hs.summable
  rwa [hs.tsum_eq] at he

theorem inverse_norm (q : ℂ) (hq : ‖q‖ < 1) :
    ‖(EndpointEta.euler q)⁻¹‖ = Real.exp (inverseLog 0 q).re := by
  have he := congrArg norm (exp_inverseLog 0 q hq)
  simpa [Complex.norm_exp, EndpointEulerTail.tailEuler, EndpointEta.euler] using he.symm

theorem norm_decay (q : ℂ) (hq : ‖q‖ < 1) (B : ℝ) (hB : B ≤ totalLoss q) :
    ‖(EndpointEta.euler q)⁻¹‖ ≤
      ‖(EndpointEta.euler (‖q‖:ℂ))⁻¹‖ * Real.exp (-B) := by
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  rw [inverse_norm q hq, inverse_norm _ hr, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold totalLoss at hB
  linarith

end
end Borwein.InverseEulerLoss
