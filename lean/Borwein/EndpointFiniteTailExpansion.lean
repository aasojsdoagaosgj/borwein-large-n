import Borwein.EndpointTailMain
import Borwein.ComplexKernelBridge

set_option autoImplicit false

namespace Borwein.EndpointFiniteTailExpansion
noncomputable section
open Complex EndpointSharpTail EndpointTailMain

def tailError (n : ℕ) (ξ w : ℂ) : ℂ := ∑' l : ℕ, errorTerm n ξ w l

theorem x_norm (n : ℕ) (w : ℂ) : ‖x n w‖ = Real.exp (-((5*n:ℕ):ℝ)*w.re) := by
  simp [x, Complex.norm_exp, Complex.mul_re]

theorem tail_error_bound (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    ‖tailError n ξ w‖ ≤ 5*‖w‖*Real.exp (-((5*n:ℕ):ℝ)*w.re)/
      (1-Real.exp (-((5*n:ℕ):ℝ)*w.re)) := by
  simpa only [tailError, x_norm] using sharp_error_bound n ξ w hξ.pow_eq_one hn hw hi

theorem tailLog_eq (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    EndpointTailLog.tailLog n (ξ*exp (-w)) =
      lambda (x n w)/(5*w)+phase ξ (x n w)+tailError n ξ w := by
  rw [tailLog_decomposition n ξ w hξ.pow_eq_one hn hw hi, main_sum n ξ w hξ hn hw hi]
  rfl

theorem radial_exponent (n : ℕ) (w : ℂ) (hn : 0 < n) (hw : 0 < w.re) :
    (2*(Real.pi:ℂ)^2/75)/w+lambda (x n w)/(5*w) =
      (n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  have hp : 0 < (((5*n:ℕ):ℂ)*w).re := by
    simpa using mul_pos (by positivity : (0:ℝ)<((5*n:ℕ):ℝ)) hw
  rw [ComplexKernelBridge.complexR_eq_dilog _ hp]
  have hx : exp (-(((5*n:ℕ):ℂ)*w)) = x n w := by unfold x; congr 1; ring
  have hx5 : exp (-(5*(((5*n:ℕ):ℂ)*w))) = x n w^5 := by
    rw [x, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [hx, hx5]
  unfold lambda
  push_cast
  field_simp
  ring

/-- Exact finite-polynomial endpoint expansion with the common radial phase exposed. -/
theorem polynomial_expansion (n : ℕ) (j : Fin 4) (w : ℂ)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (FivePoleCircle.zeta^(j.val+1)*exp (-w))
      (Borwein.polynomial n) =
        EndpointRootAsymptotic.kappa j *
          exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6+
            phase (FivePoleCircle.zeta^(j.val+1)) (x n w)+
            tailError n (FivePoleCircle.zeta^(j.val+1)) w) *
          EndpointRootAsymptotic.correction j w := by
  rw [EndpointTailLog.polynomial_eq_G_exp n _ (EndpointFiniteConnection.root_norm j w hw),
    EndpointRootAsymptotic.four_root_expansion j w hw,
    tailLog_eq n _ w (actual_root_primitive j) hn hw hi]
  unfold EndpointRootAsymptotic.main
  have he : (2*(Real.pi:ℂ)^2/75)/w-w/6+
      (lambda (x n w)/(5*w)+phase (FivePoleCircle.zeta^(j.val+1)) (x n w)+
        tailError n (FivePoleCircle.zeta^(j.val+1)) w) =
      (n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6+
        phase (FivePoleCircle.zeta^(j.val+1)) (x n w)+tailError n (FivePoleCircle.zeta^(j.val+1)) w := by
    rw [← radial_exponent n w hn hw]
    ring
  rw [← he]
  simp only [Complex.exp_add]
  ring

end
end Borwein.EndpointFiniteTailExpansion
