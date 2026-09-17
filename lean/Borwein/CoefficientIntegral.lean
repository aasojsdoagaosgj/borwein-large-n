import Borwein.FiniteMajorArc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Borwein.CoefficientIntegral
noncomputable section
open Complex Set MeasureTheory Polynomial

def angular (p : Polynomial ℤ) (m : ℕ) (r t : ℝ) : ℂ :=
  p.eval₂ (Int.castRingHom ℂ) ((r:ℂ)*Complex.exp ((t:ℂ)*I))*Complex.exp (-(m:ℂ)*(t:ℂ)*I)

theorem angular_continuous (p : Polynomial ℤ) (m : ℕ) (r : ℝ) :
    Continuous (angular p m r) := by unfold angular; fun_prop

theorem integer_orthogonality (k m : ℕ) :
    (∫ t in (0:ℝ)..2*Real.pi, Complex.exp (((k:ℂ)-(m:ℂ))*I*(t:ℂ))) =
      if k = m then (2*Real.pi:ℂ) else 0 := by
  by_cases h : k = m
  · simp [h,Complex.real_smul]
  · have hc : ((k:ℂ)-(m:ℂ))*I ≠ 0 := mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast h)) I_ne_zero
    rw [integral_exp_mul_complex hc,if_neg h]
    have he : Complex.exp (((k:ℂ)-(m:ℂ))*I*((2*Real.pi:ℝ):ℂ)) = 1 := by
      convert! Complex.exp_int_mul_two_pi_mul_I ((k:ℤ)-(m:ℤ)) using 1
      congr 1
      push_cast
      ring
    rw [he]
    simp

theorem monomial_integral (c : ℂ) (r : ℝ) (k m : ℕ) :
    (∫ t in (0:ℝ)..2*Real.pi,
      c*((r:ℂ)*Complex.exp ((t:ℂ)*I))^k*Complex.exp (-(m:ℂ)*(t:ℂ)*I)) =
      if k = m then c*(r:ℂ)^m*(2*Real.pi:ℂ) else 0 := by
  have he (t : ℝ) : c*((r:ℂ)*Complex.exp ((t:ℂ)*I))^k*Complex.exp (-(m:ℂ)*(t:ℂ)*I) =
      (c*(r:ℂ)^k)*Complex.exp (((k:ℂ)-(m:ℂ))*I*(t:ℂ)) := by
    rw [mul_pow,← Complex.exp_nat_mul, mul_assoc, mul_assoc,← Complex.exp_add]
    have harg : (k:ℂ)*((t:ℂ)*I)+(-(m:ℂ))*(t:ℂ)*I = ((k:ℂ)-(m:ℂ))*I*(t:ℂ) := by ring
    rw [harg]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,integer_orthogonality]
  split_ifs with h
  · subst k; rfl
  · simp

theorem angular_integral (p : Polynomial ℤ) (m : ℕ) (r : ℝ) :
    (∫ t in (0:ℝ)..2*Real.pi, angular p m r t) =
      (p.coeff m:ℂ)*(r:ℂ)^m*(2*Real.pi:ℂ) := by
  let D : ℕ := max p.natDegree m+1
  have hp : p.natDegree < D := by dsimp [D]; omega
  have hm : m ∈ Finset.range D := by simp only [Finset.mem_range]; dsimp [D]; omega
  have hex (t : ℝ) : angular p m r t =
      ∑ k ∈ Finset.range D, (p.coeff k:ℂ)*((r:ℂ)*Complex.exp ((t:ℂ)*I))^k*Complex.exp (-(m:ℂ)*(t:ℂ)*I) := by
    unfold angular
    rw [Polynomial.eval₂_eq_sum_range' (Int.castRingHom ℂ) hp,Finset.sum_mul]
    rfl
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [monomial_integral]
    simp [hm]
  · intro k hk
    exact (by fun_prop : Continuous (fun t : ℝ =>
      (p.coeff k:ℂ)*((r:ℂ)*Complex.exp ((t:ℂ)*I))^k*Complex.exp (-(m:ℂ)*(t:ℂ)*I))).intervalIntegrable _ _

theorem coefficient_formula (p : Polynomial ℤ) (m : ℕ) (r : ℝ) (hr : 0 < r) :
    (p.coeff m:ℂ) = (∫ t in (0:ℝ)..2*Real.pi, angular p m r t)/((r:ℂ)^m*(2*Real.pi:ℂ)) := by
  rw [angular_integral]
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hp0 : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem borwein_coefficient_formula (n m : ℕ) (r : ℝ) (hr : 0 < r) :
    ((Borwein.polynomial n).coeff m:ℂ) =
      (∫ t in (0:ℝ)..2*Real.pi, angular (Borwein.polynomial n) m r t)/((r:ℂ)^m*(2*Real.pi:ℂ)) :=
  coefficient_formula _ m r hr

end
end Borwein.CoefficientIntegral
