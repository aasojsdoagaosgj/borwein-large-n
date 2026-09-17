import Borwein.FifthRootCoordinates
import Borwein.SmallAngleBounds
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Borwein.FifthRootSeparation
noncomputable section
open Complex Set

def rotated (ξ : ℂ) (v : ℝ) : ℂ := ξ*Complex.exp ((v:ℂ)*Complex.I)

theorem rotated_norm (ξ : ℂ) (hξ : ξ^5 = 1) (v : ℝ) : ‖rotated ξ v‖ = 1 := by
  simp [rotated,Complex.norm_exp,FiveRootProductExpansion.root_norm ξ hξ]

theorem rotated_real (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) (v : ℝ) (hv : |v| ≤ 2/5) :
    (rotated ξ v).re ≤ 33/50 := by
  have h := SmallAngleBounds.perturbed_real_budget ξ.re ξ.im v
    (FifthRootCoordinates.real_upper ξ hξ hne) (FifthRootCoordinates.imaginary_upper ξ hξ hne) hv
  simpa [rotated,Complex.mul_re] using h

theorem radial_distance (u : ℂ) (hu : ‖u‖ = 1) (hr : u.re ≤ 33/50) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (3/4:ℝ) ≤ ‖1-(ρ:ℂ)*u‖ := by
  have hs : u.re^2+u.im^2 = 1 := by
    have h := Complex.sq_norm u
    rw [hu] at h
    simpa [Complex.normSq_apply,pow_two] using h.symm
  have hm := congrArg (fun t : ℝ => ρ^2*t) hs
  have hn := Complex.sq_norm (1-(ρ:ℂ)*u)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,zero_sub,add_zero] at hn
  have hp := mul_nonneg hρ (sub_nonneg.mpr hr)
  nlinarith [sq_nonneg (ρ-33/50),norm_nonneg (1-(ρ:ℂ)*u)]

theorem rotated_radial_distance (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1)
    (v ρ : ℝ) (hv : |v| ≤ 2/5) (hρ : 0 ≤ ρ) :
    (3/4:ℝ) ≤ ‖1-(ρ:ℂ)*rotated ξ v‖ :=
  radial_distance _ (rotated_norm ξ hξ v) (rotated_real ξ hξ hne v hv) ρ hρ

theorem factor_polar (ξ z : ℂ) (x : ℝ) :
    LogFactorDerivatives.w ξ z x =
      (Real.exp (-z.re*x):ℂ)*rotated ξ (-z.im*x) := by
  unfold LogFactorDerivatives.w rotated
  rw [Complex.exp_eq_exp_re_mul_sin_add_cos (-z*(x:ℂ)),
    Complex.exp_eq_exp_re_mul_sin_add_cos (((-z.im*x:ℝ):ℂ)*Complex.I)]
  simp [Complex.mul_re,Complex.mul_im]
  ring

theorem factor_gap (ξ z : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) (hz : |z.im| ≤ 2/5)
    (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    (3/4:ℝ) ≤ ‖LogFactorDerivatives.kernel ξ z x‖ := by
  have hv : |-z.im*x| ≤ 2/5 := by
    rw [abs_mul,abs_neg,abs_of_nonneg hx.1]
    simpa using mul_le_mul hz hx.2 hx.1 (by norm_num : (0:ℝ) ≤ 2/5)
  unfold LogFactorDerivatives.kernel
  rw [factor_polar]
  exact rotated_radial_distance ξ hξ hne _ _ hv (Real.exp_pos _).le

theorem coefficient_gap (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hz : |z.im| ≤ 2/5)
    (j : Fin 4) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    (3/4:ℝ) ≤ ‖LogFactorDerivatives.kernel (FiveRootProductExpansion.coefficients ξ j) z x‖ := by
  apply factor_gap _ z _ _ hz x hx
  · unfold FiveRootProductExpansion.coefficients
    rw [← pow_mul,mul_comm (j.val+1) 5,pow_mul,hξ.pow_eq_one,one_pow]
  · exact hξ.pow_ne_one_of_pos_of_lt (by omega) (by have h := j.isLt; omega)

theorem small_box_expansion (ξ z : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 11/2) (hi : |z.im| ≤ 2/5) (n : ℕ) (hn : 0 < n) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (FiveRootProductExpansion.point ξ z n) (Borwein.polynomial n) =
      Complex.exp (LogFactorDerivatives.fourMain (FiveRootProductExpansion.coefficients ξ) z n+
        LogFactorDerivatives.fourRemainder (FiveRootProductExpansion.coefficients ξ) z n) ∧
      ‖LogFactorDerivatives.fourRemainder (FiveRootProductExpansion.coefficients ξ) z n‖ ≤ 3400/(n:ℝ)^2 :=
  FiveRootProductExpansion.polynomial_expansion_3400 ξ z hξ.pow_eq_one hz0
    (FiveRootProductExpansion.small_box_norm z hz0 hz1 hi) (coefficient_gap ξ z hξ hi) n hn

end
end Borwein.FifthRootSeparation
