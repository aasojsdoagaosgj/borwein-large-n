import Borwein.RadialVarianceLower
import Borwein.SharpOuterTail

set_option autoImplicit false

namespace Borwein.CertifiedMiddleTail
noncomputable section
open RadialDerivatives SaddleArcConnection

theorem endpoint_bound :
    (1536/5:ℝ)*Real.exp (-(13/250)*(31147/81)+7200/31147) ≤ 1/1000000 := by
  have he : Real.exp ((-(13/250:ℝ)*(31147/81)+7200/31147)/32) ≤ 27/50 := by
    apply (ExpCertificate.exp_enclosure _ 0 (27/50) 12
      (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum, ExpCertificate.remainder,
      Finset.sum_range_succ, Nat.factorial]
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 32
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  have hid : Real.exp (-(13/250:ℝ)*(31147/81)+7200/31147) =
      Real.exp ((32:ℕ)*((-(13/250:ℝ)*(31147/81)+7200/31147)/32)) := by congr 1; ring
  rw [hid]
  have hp' : Real.exp ((32:ℕ)*((-(13/250:ℝ)*(31147/81)+7200/31147)/32)) ≤ (27/50:ℝ)^32 := by
    norm_num
    exact hp
  exact (mul_le_mul_of_nonneg_left hp' (by norm_num : (0:ℝ) ≤ 1536/5)).trans (by norm_num)

theorem uniform_bound (n : ℕ) (τ : ℝ) (hn : 31147 ≤ n)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    MiddlePolynomialIntegral.error n τ ≤ (1/1000000:ℝ) := by
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hV := RadialVarianceLower.uniform_lower τ hτ hT
  have hnv : (31147/81:ℝ) ≤ (n:ℝ)*secondDerivative τ := by
    have h := mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg n)
    nlinarith
  let x : ℝ := (n:ℝ)*secondDerivative τ/(31147/81)
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hnx : (n:ℝ)*secondDerivative τ = (31147/81)*x := by dsimp [x]; ring
  have hsq : Real.sqrt ((n:ℝ)*secondDerivative τ/(2*Real.pi)) ≤ 8*x := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)).mpr
      have hxx : x ≤ x^2 := by nlinarith
      have hπ := Real.pi_gt_d2
      have hp := mul_le_mul_of_nonneg_right hπ.le (sq_nonneg x)
      nlinarith
  have hc : 7200/(n:ℝ) ≤ (7200/31147:ℝ) := by
    apply (div_le_iff₀ hn0).mpr
    nlinarith
  have he : x ≤ Real.exp (x-1) := by linarith [Real.add_one_le_exp (x-1)]
  have hdecay : x*Real.exp (-(13/250)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ)) ≤
      Real.exp (-(13/250:ℝ)*(31147/81)+7200/31147) := by
    apply (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  unfold MiddlePolynomialIntegral.error
  have hp := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 192/5)
  have hp' := mul_le_mul_of_nonneg_right hp
    (Real.exp_pos (-(13/250)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ))).le
  have hd := mul_le_mul_of_nonneg_left hdecay (by norm_num : (0:ℝ) ≤ 1536/5)
  exact (show (192/5)*Real.sqrt ((n:ℝ)*secondDerivative τ/(2*Real.pi))*
      Real.exp (-(13/250)*(n:ℝ)*secondDerivative τ+7200/(n:ℝ)) ≤
      (1536/5)*Real.exp (-(13/250:ℝ)*(31147/81)+7200/31147) by nlinarith).trans endpoint_bound

theorem coefficient_error (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ (2/5) 31147+
      (127/2000000:ℝ) := by
  have h := SharpOuterTail.coefficient_error n m τ hn hτ hT hs
  have hm := uniform_bound n τ hn hτ hT
  linarith

end
end Borwein.CertifiedMiddleTail
