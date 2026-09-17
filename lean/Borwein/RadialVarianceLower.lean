import Borwein.CentralMoments
import Borwein.ExpCertificate

set_option autoImplicit false

namespace Borwein.RadialVarianceLower
noncomputable section
open RadialMoments RadialDerivatives PhaseGap GroupedWeights

theorem variance_formula (y : ℝ) :
    variance y =
      (Real.exp (-y) + 4*Real.exp (-y)^2 + 10*Real.exp (-y)^3 +
        20*Real.exp (-y)^4 + 10*Real.exp (-y)^5 + 4*Real.exp (-y)^6 +
        Real.exp (-y)^7) / denominator (Real.exp (-y))^2 := by
  have hd := (denominator_pos (Real.exp (-y)) (Real.exp_pos _).le).ne'
  unfold variance
  rw [second_eq_weighted, mean_eq_weighted]
  simp only [radialWeight_eq_power, Fin.sum_univ_five]
  norm_num only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, pow_zero, pow_one, zero_mul, zero_pow, one_mul, zero_add]
  field_simp
  unfold denominator
  ring

theorem variance_lower (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y) + Real.exp (-y)^2 ≤ variance y := by
  let q := Real.exp (-y)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd := sq_pos_of_pos (denominator_pos q hq)
  rw [variance_formula]
  change q+q^2 ≤ (q+4*q^2+10*q^3+20*q^4+10*q^5+4*q^6+q^7)/denominator q^2
  apply (le_div_iff₀ hd).mpr
  have hp : 0 ≤ q^2*(1-q)*(1+6*q+19*q^2+20*q^3+15*q^4+9*q^5+4*q^6+q^7) :=
    mul_nonneg (mul_nonneg (sq_nonneg q) (by linarith)) (by positivity)
  have hid : (q+4*q^2+10*q^3+20*q^4+10*q^5+4*q^6+q^7) -
      (q+q^2)*denominator q^2 =
      q^2*(1-q)*(1+6*q+19*q^2+20*q^3+15*q^4+9*q^5+4*q^6+q^7) := by
    unfold denominator
    ring
  linarith

theorem exponential_second_moment (c : ℝ) (hc : c ≠ 0) :
    (∫ x in (0:ℝ)..1, x^2*Real.exp (-c*x)) =
      2/c^3-(1/c+2/c^2+2/c^3)*Real.exp (-c) := by
  let F := fun x : ℝ => -(x^2/c+2*x/c^2+2/c^3)*Real.exp (-c*x)
  have hd (x : ℝ) : HasDerivAt F (x^2*Real.exp (-c*x)) x := by
    have h := (((((hasDerivAt_id x).pow 2).div_const c).add
      (((hasDerivAt_id x).const_mul 2).div_const (c^2))).add_const (2/c^3)).neg.mul
        (((hasDerivAt_id x).const_mul (-c)).exp)
    apply h.congr_deriv
    dsimp
    field_simp
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x)
    ((by fun_prop : Continuous (fun x : ℝ => x^2*Real.exp (-c*x))).intervalIntegrable 0 1)
  change (∫ x in (0:ℝ)..1, x^2*Real.exp (-c*x)) = F 1-F 0 at he
  rw [he]
  dsimp [F]
  norm_num
  ring

theorem exp_endpoint : Real.exp (-(11/2:ℝ)) ≤ 1/240 := by
  have he : Real.exp (-(11/16:ℝ)) ≤ 503/1000 := by
    apply (ExpCertificate.exp_enclosure _ 0 (503/1000) 12
      (by norm_num) (by norm_num) ?_ ?_).2
    all_goals norm_num [ExpCertificate.taylorSum, ExpCertificate.remainder,
      Finset.sum_range_succ, Nat.factorial]
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le he 8
  rw [← Real.exp_nat_mul] at hp
  norm_num at hp
  exact hp.trans (by norm_num)

theorem uniform_lower (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    (1/81:ℝ) ≤ secondDerivative τ := by
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
      x^2*(Real.exp (-(11/2)*x)+Real.exp (-11*x)) ≤ secondDensity τ x := by
    have h := variance_lower (τ*x) (mul_nonneg hτ hx.1)
    have htx := mul_le_mul_of_nonneg_right hT hx.1
    have he : Real.exp (-(11/2)*x) ≤ Real.exp (-(τ*x)) :=
      Real.exp_le_exp.mpr (by linarith)
    have he2 := pow_le_pow_left₀ (Real.exp_pos _).le he 2
    rw [← Real.exp_nat_mul] at he2
    have hid : Real.exp (-11*x) = Real.exp ((2:ℕ)*(-(11/2)*x)) := by congr 1; ring
    rw [hid]
    unfold secondDensity
    exact mul_le_mul_of_nonneg_left (by nlinarith :
      Real.exp (-(11/2)*x)+Real.exp ((2:ℕ)*(-(11/2)*x)) ≤ variance (τ*x)) (sq_nonneg x)
  have hi := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (by norm_num : (0:ℝ) ≤ 1)
    ((by fun_prop : Continuous (fun x : ℝ =>
      x^2*(Real.exp (-(11/2)*x)+Real.exp (-11*x)))).intervalIntegrable 0 1)
    ((continuous_secondDensity τ).intervalIntegrable 0 1) hpoint
  have he2 := pow_le_pow_left₀ (Real.exp_pos _).le exp_endpoint 2
  rw [← Real.exp_nat_mul] at he2
  norm_num at he2
  have hint : (∫ x in (0:ℝ)..1, x^2*(Real.exp (-(11/2)*x)+Real.exp (-11*x))) =
      (18-346*Real.exp (-(11/2))-145*Real.exp (-11))/1331 := by
    simp_rw [mul_add]
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous (fun x : ℝ => x^2*Real.exp (-(11/2)*x))).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun x : ℝ => x^2*Real.exp (-11*x))).intervalIntegrable 0 1)]
    rw [exponential_second_moment (11/2) (by norm_num), exponential_second_moment 11 (by norm_num)]
    ring
  rw [hint] at hi
  change _ ≤ secondDerivative τ at hi
  have he := exp_endpoint
  linarith

end
end Borwein.RadialVarianceLower
