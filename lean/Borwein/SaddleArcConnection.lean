import Borwein.CoefficientIntegral
import Borwein.FivePoleCircle

namespace Borwein.SaddleArcConnection
noncomputable section
open Complex Set MeasureTheory CoefficientIntegral FiveRootProductExpansion CombinedAmplitude
  FivePoleCircle RadialDerivatives

def center (j : Fin 4) : ℝ := 2*Real.pi*(j.val+1)/5
def radius (n : ℕ) (τ : ℝ) : ℝ := Real.exp (-τ/(5*n))
def arcSum (n m : ℕ) (τ h : ℝ) : ℂ :=
  ∑ j : Fin 4, ∫ u in center j-h/(5*n)..center j+h/(5*n),
    angular (Borwein.polynomial n) m (radius n τ) u

theorem coefficient_eq_exp_center (j : Fin 4) :
    coefficients zeta j = Complex.exp ((center j:ℂ)*I) := by
  unfold coefficients zeta
  rw [AngularKernel.circle_eq_exp,← Complex.exp_nat_mul]
  congr 1
  unfold center
  push_cast
  ring

theorem fifth_power_reduction (ξ : ℂ) (hξ : ξ^5 = 1) (m : ℕ) : ξ^m = ξ^(m%5) := by
  conv_lhs => rw [← Nat.mod_add_div m 5]
  rw [pow_add,pow_mul,hξ,one_pow,mul_one]

theorem angular_phase_weight (j : Fin 4) (m : ℕ) :
    Complex.exp (-(m:ℂ)*(center j:ℂ)*I) = phaseWeight zeta (m%5) j := by
  have hξ := (coefficient_primitive zeta zeta_primitive j).pow_eq_one
  have he : -(m:ℂ)*(center j:ℂ)*I = -((m:ℂ)*((center j:ℂ)*I)) := by ring
  rw [he,Complex.exp_neg,Complex.exp_nat_mul,← coefficient_eq_exp_center]
  unfold phaseWeight
  rw [zpow_neg,zpow_natCast,fifth_power_reduction _ hξ m]

theorem rotated_point (j : Fin 4) (n : ℕ) (τ t : ℝ) :
    (radius n τ:ℂ)*Complex.exp (((center j+t/(5*n):ℝ):ℂ)*I) =
      point (coefficients zeta j) ((τ:ℂ)-(t:ℂ)*I) n := by
  unfold radius point
  rw [Complex.ofReal_exp,coefficient_eq_exp_center,← Complex.exp_add,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem rotated_angular (j : Fin 4) (n m : ℕ) (τ t : ℝ) :
    angular (Borwein.polynomial n) m (radius n τ) (center j+t/(5*n)) =
      Complex.exp (-(m:ℂ)*(t:ℂ)/(5*(n:ℂ))*I)*phaseWeight zeta (m%5) j*
        Polynomial.eval₂ (Int.castRingHom ℂ)
          (point (coefficients zeta j) ((τ:ℂ)-(t:ℂ)*I) n) (Borwein.polynomial n) := by
  unfold angular
  rw [rotated_point]
  have he : -(m:ℂ)*(((center j+t/(5*n):ℝ):ℂ))*I =
      -(m:ℂ)*(center j:ℂ)*I+(-(m:ℂ)*(t:ℂ)/(5*(n:ℂ))*I) := by push_cast; ring
  rw [he,Complex.exp_add,angular_phase_weight]
  ring

theorem saddle_exponent (n m : ℕ) (τ t : ℝ) (hn : 0 < n)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    -(m:ℂ)*(t:ℂ)/(5*(n:ℂ))*I = (n:ℂ)*(firstDerivative τ:ℂ)*(t:ℂ)*I := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hc := congrArg (fun x : ℝ => (x:ℂ)) hs
  push_cast at hc
  have hf : (firstDerivative τ:ℂ) = -(m:ℂ)/(5*(n:ℂ)^2) := by linear_combination -hc
  rw [hf]
  field_simp

theorem sum_rotated_angular (n m : ℕ) (τ t : ℝ) (hn : 0 < n)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    (∑ j : Fin 4, angular (Borwein.polynomial n) m (radius n τ) (center j+t/(5*n))) =
      Complex.exp ((n:ℂ)*PhaseIntegral.complexR (τ:ℂ))*FiniteMajorArc.integrand zeta (m%5) n τ t := by
  simp_rw [rotated_angular,saddle_exponent n m τ t hn hs,mul_assoc]
  rw [← Finset.mul_sum]
  unfold FiniteMajorArc.integrand
  conv_rhs => rw [← mul_assoc,← Complex.exp_add]
  congr 2
  ring

theorem arc_change_variable (f : ℝ → ℂ) (θ c h : ℝ) :
    (∫ u in θ-h/c..θ+h/c, f u) = (c:ℂ)⁻¹*(∫ t in -h..h, f (θ+t/c)) := by
  simpa only [neg_div,sub_eq_add_neg,Complex.real_smul,Complex.ofReal_inv] using
    (intervalIntegral.inv_smul_integral_comp_add_div (a := -h) (b := h) f c θ).symm

theorem arcSum_integral (n m : ℕ) (τ h : ℝ) (hn : 0 < n)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    arcSum n m τ h = Complex.exp ((n:ℂ)*PhaseIntegral.complexR (τ:ℂ))/(5*(n:ℂ))*
      (∫ t in -h..h, FiniteMajorArc.integrand zeta (m%5) n τ t) := by
  unfold arcSum
  simp_rw [arc_change_variable]
  rw [← Finset.mul_sum,← intervalIntegral.integral_finsetSum]
  · simp_rw [sum_rotated_angular n m τ _ hn hs]
    rw [intervalIntegral.integral_const_mul]
    push_cast
    ring
  · intro j hj
    exact ((angular_continuous (Borwein.polynomial n) m (radius n τ)).comp
      (by fun_prop : Continuous (fun t : ℝ => center j+t/(5*n)))).intervalIntegrable _ _

def majorContribution (n m : ℕ) (τ h : ℝ) : ℂ :=
  arcSum n m τ h/((radius n τ:ℂ)^m*(2*Real.pi:ℂ))

def bulkScale (n m : ℕ) (τ : ℝ) : ℝ :=
  Real.exp ((n:ℝ)*PhaseIntegral.radialR τ)*GaussianNormalization.scale n τ/
    (5*(n:ℝ)*(radius n τ)^m*(2*Real.pi))

theorem bulkScale_pos (n m : ℕ) (τ : ℝ) (hn : 0 < n) : 0 < bulkScale n m τ := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs := GaussianNormalization.scale_pos n τ hn0
  unfold bulkScale radius
  positivity [Real.pi_pos]

theorem normalized_contribution (n m : ℕ) (τ h : ℝ) (hn : 0 < n)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    majorContribution n m τ h/(bulkScale n m τ:ℂ) =
      (∫ t in -h..h, FiniteMajorArc.integrand zeta (m%5) n τ t)/(GaussianNormalization.scale n τ:ℂ) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hrr : radius n τ ≠ 0 := (Real.exp_pos _).ne'
  have hr0 : (radius n τ:ℂ) ≠ 0 := by exact_mod_cast hrr
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have he0 : Complex.exp ((n:ℂ)*(PhaseIntegral.radialR τ:ℂ)) ≠ 0 := Complex.exp_ne_zero _
  unfold majorContribution bulkScale
  rw [arcSum_integral n m τ h hn hs,SmallBoxPhaseDecay.complexR_real]
  push_cast
  field_simp

theorem major_contribution_error (n m : ℕ) (τ h N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5)
    (hs : -firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖majorContribution n m τ h/(bulkScale n m τ:ℂ)-psi zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError zeta (m%5) n τ h N := by
  have hn0 : 0 < (n:ℝ) := hN.trans_le hn
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hscale := GaussianNormalization.scale_pos n τ hn0
  have hc : (GaussianNormalization.scale n τ:ℂ) ≠ 0 := by exact_mod_cast hscale.ne'
  rw [normalized_contribution n m τ h hnNat hs]
  have he (J A : ℂ) : J/(GaussianNormalization.scale n τ:ℂ)-A =
      (J-A*(GaussianNormalization.scale n τ:ℂ))/(GaussianNormalization.scale n τ:ℂ) := by field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_of_nonneg hscale.le]
  exact FiniteMajorArc.normalized_major_arc zeta zeta_primitive (m%5) n τ h N hN hn hτ0 hτ1 hh0 hh1

theorem radius_power (n m : ℕ) (τ : ℝ) :
    (radius n τ)^m = Real.exp (-(m:ℝ)*τ/(5*n)) := by
  unfold radius
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem gaussian_scale_product (n : ℕ) (τ : ℝ) (hn : 0 < n) :
    GaussianNormalization.scale n τ*Real.sqrt (n:ℝ)*Real.sqrt (2*Real.pi*secondDerivative τ) = 2*Real.pi := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hV := secondDerivative_pos τ
  unfold GaussianNormalization.scale
  rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi/((n:ℝ)*secondDerivative τ)),
    ← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi/((n:ℝ)*secondDerivative τ)*(n:ℝ))]
  have he : (2*Real.pi/((n:ℝ)*secondDerivative τ)*(n:ℝ))*(2*Real.pi*secondDerivative τ) = (2*Real.pi)^2 := by
    field_simp
  rw [he,Real.sqrt_sq (by positivity)]

theorem bulkScale_formula (n m : ℕ) (τ : ℝ) (hn : 0 < n) :
    bulkScale n m τ = Real.exp ((n:ℝ)*PhaseIntegral.radialR τ+(m:ℝ)*τ/(5*n))/
      (5*(n:ℝ)*Real.sqrt (n:ℝ)*Real.sqrt (2*Real.pi*secondDerivative τ)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hr0 : radius n τ ≠ 0 := (Real.exp_pos _).ne'
  have hs0 : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hv0 : Real.sqrt (2*Real.pi*secondDerivative τ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity [secondDerivative_pos τ])).ne'
  have hex : Real.exp ((n:ℝ)*PhaseIntegral.radialR τ) =
      Real.exp ((n:ℝ)*PhaseIntegral.radialR τ+(m:ℝ)*τ/(5*n))*(radius n τ)^m := by
    rw [radius_power,← Real.exp_add]
    congr 1
    ring
  have hs := gaussian_scale_product n τ hn
  unfold bulkScale
  rw [hex]
  field_simp
  nlinarith [hs]

end
end Borwein.SaddleArcConnection
