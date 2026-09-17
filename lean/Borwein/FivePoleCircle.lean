import Borwein.FivePoleDecomposition
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace Borwein.FivePoleCircle
noncomputable section
open scoped BigOperators
open AngularKernel

def zeta : ℂ := circle (2*Real.pi/5)

theorem zeta_primitive : IsPrimitiveRoot zeta 5 := by
  have he : zeta = Complex.exp (2*(Real.pi:ℂ)*Complex.I/5) := by
    rw [zeta, circle_eq_exp]
    congr 1
    push_cast
    ring
  rw [he]
  exact Complex.isPrimitiveRoot_exp 5 (by norm_num)

theorem rotated_circle (u : ℝ) (j : ℕ) :
    zeta^j*circle u = circle (u+2*Real.pi*j/5) := by
  rw [zeta, circle_pow, ← PoleVariation.circle_add]
  congr 1
  ring

theorem circle_fifth_ne_one (u : ℝ) (hu : Real.sin (5*u/2) ≠ 0) :
    (circle u)^5 ≠ 1 := by
  rw [circle_pow]
  norm_num only [Nat.cast_ofNat]
  have h := radial_factor_ne_zero 1 (5*u) (by norm_num) hu
  norm_num only [Complex.ofReal_one, one_mul] at h
  exact (sub_ne_zero.mp h).symm

theorem circle_decomposition (u : ℝ) (hu : Real.sin (5*u/2) ≠ 0) :
    FiniteFourierKernel.kernel (circle u) =
      (4/5:ℂ)*PoleVariation.pole u-
      (1/5:ℂ)*∑ j : Fin 4, PoleVariation.pole (u+2*Real.pi*(j.val+1)/5) := by
  have h := FivePoleDecomposition.five_pole_decomposition zeta (circle u)
    zeta_primitive (circle_fifth_ne_one u hu)
  simp_rw [rotated_circle] at h
  simpa only [PoleVariation.pole, Nat.cast_add, Nat.cast_one] using h

theorem circle_variation (u v : ℝ) (hu : Real.sin (5*u/2) ≠ 0)
    (hv : Real.sin (5*v/2) ≠ 0) :
    ‖FiniteFourierKernel.kernel (circle u)-FiniteFourierKernel.kernel (circle v)‖ ≤
      (4/5:ℝ)*‖PoleVariation.pole u-PoleVariation.pole v‖+
      (1/5:ℝ)*∑ j : Fin 4, ‖PoleVariation.pole (u+2*Real.pi*(j.val+1)/5)-
        PoleVariation.pole (v+2*Real.pi*(j.val+1)/5)‖ := by
  have h := FivePoleDecomposition.kernel_variation zeta (circle u) (circle v)
    zeta_primitive (circle_fifth_ne_one u hu) (circle_fifth_ne_one v hv)
  simp_rw [rotated_circle] at h
  simpa only [PoleVariation.pole, Nat.cast_add, Nat.cast_one] using h

theorem profile_variation (u v : ℝ) (hu : Real.sin (5*u/2) ≠ 0)
    (hv : Real.sin (5*v/2) ≠ 0) :
    |RadialKernelProfile.profile u-RadialKernelProfile.profile v| ≤
      (8/5:ℝ)*‖PoleVariation.pole u-PoleVariation.pole v‖+
      (2/5:ℝ)*∑ j : Fin 4, ‖PoleVariation.pole (u+2*Real.pi*(j.val+1)/5)-
        PoleVariation.pole (v+2*Real.pi*(j.val+1)/5)‖ := by
  rw [← RadialKernelProfile.unit_profile u, ← RadialKernelProfile.unit_profile v,
    ← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := (abs_norm_sub_norm_le (FiniteFourierKernel.kernel (circle u))
    (FiniteFourierKernel.kernel (circle v))).trans (circle_variation u v hu hv)
  have hh := mul_le_mul_of_nonneg_left h (by norm_num : (0:ℝ) ≤ 2)
  nlinarith

end
end Borwein.FivePoleCircle
