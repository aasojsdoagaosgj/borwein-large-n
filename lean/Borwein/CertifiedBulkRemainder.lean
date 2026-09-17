import Borwein.CertifiedMiddleTail

set_option autoImplicit false

namespace Borwein.CertifiedBulkRemainder
noncomputable section
open RadialDerivatives EMUniformBounds CombinedAmplitude GaussianNormalization SaddleArcConnection

/-- The two remaining first-order budgets, retaining the combined amplitude. -/
def mainBudget (ζ : ℂ) (a : ℕ) (τ : ℝ) : ℝ :=
  errorCoefficient ζ a τ+thetaBudget ζ a τ (2/5)/Real.sqrt (39/50:ℝ)

theorem correction_radius (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    Dstar τ (2/5) ≤ 1 := by
  have hr : EMUniformBounds.radius τ (2/5) ≤ 6 := by
    unfold EMUniformBounds.radius
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  have he : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold Dstar
  have hm := mul_le_mul hr (show (1/30:ℝ)+(8/75)*Real.exp (-τ) ≤ 7/50 by linarith)
    (by positivity) (by norm_num : (0:ℝ) ≤ 6)
  exact hm.trans (by norm_num)

theorem residual_budget (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    residualBudget τ (2/5) 31147 ≤ 21000 := by
  have hd := correction_radius τ hτ hT
  have hd0 := Dstar_nonneg τ (2/5)
  have hd2 : (Dstar τ (2/5))^2 ≤ 1 := by nlinarith
  have he0 : Real.exp (1/2000:ℝ) ≤ 1001/1000 := by
    apply (ExpCertificate.exp_enclosure _ 0 (1001/1000) 6
      (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum, ExpCertificate.remainder,
      Finset.sum_range_succ, Nat.factorial]
  have he : Real.exp (Dstar τ (2/5)/31147+3400/(31147:ℝ)^2) ≤ 1001/1000 :=
    (Real.exp_le_exp.mpr (by linarith : Dstar τ (2/5)/31147+3400/(31147:ℝ)^2 ≤ 1/2000)).trans he0
  unfold residualBudget
  have hp := mul_le_mul (show (154/25:ℝ)*(3400+(Dstar τ (2/5))^2/2) ≤
      (154/25)*(3400+1/2) by linarith) he (Real.exp_pos _).le (by norm_num)
  exact hp.trans (by norm_num)

theorem residual_normalized (n : ℕ) (τ : ℝ) (hn : 31147 ≤ n)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    residualBudget τ (2/5) 31147/((n:ℝ)^2*Real.sqrt (39/50:ℝ)) ≤ (1/40000:ℝ) := by
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hs : (22/25:ℝ) ≤ Real.sqrt (39/50:ℝ) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
    norm_num
  have hn2 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 31147) hn' 2
  have hp := mul_le_mul hn2 hs (by norm_num : (0:ℝ) ≤ 22/25) (sq_nonneg (n:ℝ))
  apply (div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ)^2*Real.sqrt (39/50:ℝ))).mpr
  have hb := residual_budget τ hτ hT
  nlinarith

theorem gaussian_endpoint :
    4*Real.exp (-(2/2025:ℝ)*31147) ≤ 1/1000000000000 := by
  have he : Real.exp (-(2/2025:ℝ)*31147/32) ≤ 2/5 := by
    apply (ExpCertificate.exp_enclosure _ 0 (2/5) 12
      (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum, ExpCertificate.remainder,
      Finset.sum_range_succ, Nat.factorial]
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 32
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have he' : Real.exp (-(2/2025:ℝ)*31147) ≤ (2/5:ℝ)^32 := by norm_num; exact hp
  exact (mul_le_mul_of_nonneg_left he' (by norm_num : (0:ℝ) ≤ 4)).trans (by norm_num)

theorem gaussian_normalized (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ : ℝ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    ‖psi ζ a (τ:ℂ)‖*Real.exp (-(n:ℝ)*secondDerivative τ*(2/5:ℝ)^2/2) ≤
      (1/1000000000000:ℝ) := by
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have ha := FullGaussianReplacement.psi_real_norm_le_four ζ hζ a τ hτ
  have ht := FullGaussianReplacement.tail_from_variance_lower (n:ℝ) (secondDerivative τ)
    (2/5) (1/81) (2/2025) (Nat.cast_nonneg n)
    (RadialVarianceLower.uniform_lower τ hτ hT) (by norm_num)
  have he : 4*Real.exp (-(2/2025)*(n:ℝ)) ≤ 4*Real.exp (-(2/2025:ℝ)*31147) := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
    exact Real.exp_le_exp.mpr (by linarith)
  exact ((mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le).trans ht).trans
    (he.trans gaussian_endpoint)

theorem main_error (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a n : ℕ) (τ : ℝ)
    (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    FiniteMajorArc.normalizedError ζ a n τ (2/5) 31147 ≤ mainBudget ζ a τ/(n:ℝ)+
      (1/40000:ℝ)+1/1000000000000 := by
  have hr := residual_normalized n τ hn hτ hT
  have hg := gaussian_normalized ζ hζ a n τ hn hτ hT
  have hid : mainBudget ζ a τ/(n:ℝ) = errorCoefficient ζ a τ/(n:ℝ)+
      thetaBudget ζ a τ (2/5)/((n:ℝ)*Real.sqrt (39/50:ℝ)) := by
    unfold mainBudget
    ring
  rw [hid]
  unfold FiniteMajorArc.normalizedError
  linarith

theorem coefficient_error (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      mainBudget FivePoleCircle.zeta (m%5) τ/(n:ℝ)+(9/100000:ℝ) := by
  have h := CertifiedMiddleTail.coefficient_error n m τ hn hτ hT hs
  have hm := main_error FivePoleCircle.zeta FivePoleCircle.zeta_primitive (m%5) n τ hn hτ hT
  linarith

end
end Borwein.CertifiedBulkRemainder
