import Borwein.PeriodicEulerProduct

set_option autoImplicit false

namespace Borwein.PeriodicLossSeries
noncomputable section
open Complex PeriodicEulerProduct

def powerSum (j : Fin 4) (q : ℂ) : ℂ := q^(j.val+1)/(1-q^5)
def residueLoss (j : Fin 4) (q : ℂ) : ℝ := (powerSum j (‖q‖:ℂ)).re-(powerSum j q).re
def totalLoss (b : Fin 4 → ℕ) (q : ℂ) : ℝ := ∑ j : Fin 4, (b j:ℝ)*residueLoss j q
def numerator (b : Fin 4 → ℕ) (q : ℂ) : ℂ := ∑ j : Fin 4, (b j:ℂ)*q^(j.val+1)

theorem power_hasSum (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => q^(PeriodicEulerProduct.exponent j m)) (powerSum j q) := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hs := (hasSum_geometric_of_norm_lt_one hq5).mul_left (q^(j.val+1))
  have he : q^(j.val+1)*(1-q^5)⁻¹=powerSum j q := by rfl
  rw [he] at hs
  exact hs.congr_fun (fun m => by simp only [PeriodicEulerProduct.exponent, ← pow_mul, ← pow_add]; congr 1; omega)

theorem residueLoss_hasSum (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => ‖q‖^(PeriodicEulerProduct.exponent j m)-(q^(PeriodicEulerProduct.exponent j m)).re) (residueLoss j q) := by
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  have hs := (Complex.hasSum_re (power_hasSum j (‖q‖:ℂ) hr)).sub (Complex.hasSum_re (power_hasSum j q hq))
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, residueLoss] using hs

theorem logLoss_hasSum (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    HasSum (fun m : ℕ => (log (1-q^(PeriodicEulerProduct.exponent j m))).re-(log (1-(‖q‖:ℂ)^(PeriodicEulerProduct.exponent j m))).re)
      ((residueLog j (‖q‖:ℂ)).re-(residueLog j q).re) := by
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  have hs := (Complex.hasSum_re (log_summable j q hq).hasSum).sub
    (Complex.hasSum_re (log_summable j (‖q‖:ℂ) hr).hasSum)
  have he : (∑' m : ℕ, log (1-q^(PeriodicEulerProduct.exponent j m))).re-(∑' m : ℕ, log (1-(‖q‖:ℂ)^(PeriodicEulerProduct.exponent j m))).re =
      (residueLog j (‖q‖:ℂ)).re-(residueLog j q).re := by simp only [residueLog, Complex.neg_re]; ring
  rw [he] at hs
  exact hs

theorem residue_loss_bound (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    residueLoss j q ≤ (residueLog j (‖q‖:ℂ)).re-(residueLog j q).re := by
  have hs := residueLoss_hasSum j q hq
  have ht := logLoss_hasSum j q hq
  have hp : ∀ m : ℕ, ‖q‖^(PeriodicEulerProduct.exponent j m)-(q^(PeriodicEulerProduct.exponent j m)).re ≤
      (log (1-q^(PeriodicEulerProduct.exponent j m))).re-(log (1-(‖q‖:ℂ)^(PeriodicEulerProduct.exponent j m))).re := by
    intro m
    have hqn : ‖q^(PeriodicEulerProduct.exponent j m)‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.ne_of_gt (exponent_pos j m))
    have h := PeriodicFactorLoss.first_frequency_loss (q^(PeriodicEulerProduct.exponent j m)) hqn
    rw [Complex.norm_pow] at h
    simpa only [Complex.ofReal_pow] using h
  have h := hs.summable.tsum_le_tsum hp ht.summable
  rw [hs.tsum_eq, ht.tsum_eq] at h
  exact h

theorem product_log_loss (b : Fin 4 → ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    totalLoss b q ≤ (productLog b (‖q‖:ℂ)).re-(productLog b q).re := by
  have h : ∑ j : Fin 4, (b j:ℝ)*residueLoss j q ≤
      ∑ j : Fin 4, (b j:ℝ)*((residueLog j (‖q‖:ℂ)).re-(residueLog j q).re) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (residue_loss_bound j q hq) (Nat.cast_nonneg _)
  simpa only [totalLoss, productLog, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, mul_sub, Finset.sum_sub_distrib] using h

/-- A first-frequency loss yields a modulus bound for the actual inverse Euler products. -/
theorem product_decay (b : Fin 4 → ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖product b q‖ ≤ ‖product b (‖q‖:ℂ)‖*Real.exp (-totalLoss b q) := by
  have hr : ‖(‖q‖:ℂ)‖ < 1 := by simpa using hq
  rw [product_norm b q hq, product_norm b (‖q‖:ℂ) hr, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [product_log_loss b q hq]

theorem totalLoss_quotient (b : Fin 4 → ℕ) (q : ℂ) :
    totalLoss b q = (numerator b (‖q‖:ℂ)/(1-(‖q‖:ℂ)^5)).re-(numerator b q/(1-q^5)).re := by
  simp only [totalLoss, residueLoss, numerator, Finset.sum_div, Complex.re_sum,
    ← Finset.sum_sub_distrib, mul_sub, powerSum]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : (b j:ℝ)*(powerSum j (‖q‖:ℂ)).re = ((b j:ℂ)*powerSum j (‖q‖:ℂ)).re := by simp [Complex.mul_re]
  have h2 : (b j:ℝ)*(powerSum j q).re = ((b j:ℂ)*powerSum j q).re := by simp [Complex.mul_re]
  simp only [powerSum] at h1 h2
  rw [h1, h2]
  congr 1 <;> congr 1 <;> ring

end
end Borwein.PeriodicLossSeries
