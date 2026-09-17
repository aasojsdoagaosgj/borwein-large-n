import Borwein.SharpOuterLocalization

set_option autoImplicit false

namespace Borwein.SharpOuterTail
noncomputable section
open SaddleArcConnection

theorem endpoint_bound : 15*177*31147*Real.exp (-(9/10000:ℝ)*31147) ≤ 1/16000 := by
  have he : Real.exp (-(9/10000:ℝ)*31147/32) ≤ 5/12 := by
    apply (ExpCertificate.exp_enclosure _ 0 (5/12) 12 (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 32
  have hid : Real.exp (-(9/10000:ℝ)*31147) = (Real.exp (-(9/10000:ℝ)*31147/32))^32 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hid]
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 15*177*31147)
  exact hm.trans (by norm_num)

theorem uniform_bound (n : ℕ) (hn : 31147 ≤ n) :
    15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-(9/10000)*(n:ℝ)) ≤ (1/16000:ℝ) := by
  let x : ℝ := (n:ℝ)/31147
  have hn' : (31147:ℝ) ≤ n := by exact_mod_cast hn
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hnx : (n:ℝ) = 31147*x := by dsimp [x]; ring
  have hsq : Real.sqrt (n:ℝ) ≤ 177*x := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have hxx : x ≤ x^2 := by nlinarith
      nlinarith
  have hpref : (n:ℝ)*Real.sqrt (n:ℝ) ≤ 177*31147*x^2 := by
    apply (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n)).trans_eq
    rw [hnx]
    ring
  have he : x ≤ Real.exp (x-1) := by linarith [Real.add_one_le_exp (x-1)]
  have he2 := pow_le_pow_left₀ (by linarith : 0 ≤ x) he 2
  rw [← Real.exp_nat_mul] at he2
  norm_num only [Nat.cast_ofNat] at he2
  have hdecay : x^2*Real.exp (-(9/10000)*(n:ℝ)) ≤ Real.exp (-(9/10000:ℝ)*31147) := by
    apply (mul_le_mul_of_nonneg_right he2 (Real.exp_pos _).le).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith
  have h := mul_le_mul_of_nonneg_right hpref (Real.exp_pos (-(9/10000)*(n:ℝ))).le
  have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 15)
  have hd := mul_le_mul_of_nonneg_left hdecay (by norm_num : (0:ℝ) ≤ 15*177*31147)
  exact (show 15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-(9/10000)*(n:ℝ)) ≤
      15*177*31147*Real.exp (-(9/10000:ℝ)*31147) by nlinarith).trans endpoint_bound

theorem normalized_mass (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    GapIntegralBounds.mass n τ (6/5)/((radius n τ)^m*(2*Real.pi)*bulkScale n m τ) ≤ (1/16000:ℝ) :=
  (SharpOuterLocalization.normalized_mass n m τ hn hτ hT).trans (uniform_bound n hn)

theorem coefficient_error (n m : ℕ) (τ : ℝ) (hn : 31147 ≤ n) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ (2/5) 31147+
      MiddlePolynomialIntegral.error n τ+(1/16000:ℝ) := by
  exact (SharpOuterLocalization.coefficient_error n m τ hn hτ hT hs).trans
    (add_le_add le_rfl (uniform_bound n hn))

end
end Borwein.SharpOuterTail
