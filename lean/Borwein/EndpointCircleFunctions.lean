import Borwein.EndpointCirclePartition

set_option autoImplicit false

namespace Borwein.EndpointCircleFunctions
noncomputable section
open Complex MeasureTheory EndpointCircleKernel

def polynomial (n : ℕ) (z : ℂ) : ℂ := Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n)
def difference (n : ℕ) (z : ℂ) : ℂ := polynomial n z-EndpointEta.G z
def GIntegral (m : ℕ) (v : ℝ) : ℂ := ∫ θ in (0:ℝ)..2*Real.pi, kernel EndpointEta.G m v θ

theorem polynomial_continuous (n : ℕ) (v : ℝ) : Continuous (fun θ => polynomial n (point v θ)) :=
  ((Borwein.polynomial n).continuous_eval₂ (Int.castRingHom ℂ)).comp (point_continuous v)

theorem G_continuous (v : ℝ) (hv : 0 < v) : Continuous (fun θ => EndpointEta.G (point v θ)) := by
  have hq (θ : ℝ) : ‖point v θ‖ < 1 := by rw [point_norm]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hT := EndpointTailContinuity.tail_continuous 0 (point v) (Real.exp (-v)) (point_continuous v)
    (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith)) (fun θ => (point_norm v θ).le)
  have hNZ (θ : ℝ) : EndpointFiniteConnection.tail 0 (point v θ) ≠ 0 := by
    rw [← EndpointTailLog.exp_tailLog 0 (point v θ) (hq θ)]
    exact exp_ne_zero _
  have hI (θ : ℝ) : 1/EndpointFiniteConnection.tail 0 (point v θ)=EndpointEta.G (point v θ) := by
    symm
    apply (eq_div_iff (hNZ θ)).mpr
    have hh := EndpointFiniteConnection.polynomial_eq_G_tail 0 (point v θ) (hq θ)
    simpa [Borwein.polynomial] using hh.symm
  exact (continuous_const.div hT hNZ).congr hI

theorem difference_continuous (n : ℕ) (v : ℝ) (hv : 0 < v) :
    Continuous (fun θ => difference n (point v θ)) :=
  (polynomial_continuous n v).sub (G_continuous v hv)

theorem polynomial_kernel (p : Polynomial ℤ) (m : ℕ) (v θ : ℝ) :
    kernel (fun z => p.eval₂ (Int.castRingHom ℂ) z) m v θ=
      exp ((m:ℂ)*(v:ℂ))*CoefficientIntegral.angular p m (Real.exp (-v)) θ := by
  have hp : point v θ=((Real.exp (-v):ℝ):ℂ)*exp ((θ:ℂ)*I) := by
    rw [Complex.ofReal_exp, ← exp_add]
    simp [point]
  have he : (m:ℂ)*((v:ℂ)-(θ:ℂ)*I)=(m:ℂ)*(v:ℂ)+(-(m:ℂ)*(θ:ℂ)*I) := by ring
  rw [kernel, hp, he, exp_add]
  unfold CoefficientIntegral.angular
  ring

theorem polynomial_integral (p : Polynomial ℤ) (m : ℕ) (v : ℝ) :
    (∫ θ in (0:ℝ)..2*Real.pi, kernel (fun z => p.eval₂ (Int.castRingHom ℂ) z) m v θ)=
      (p.coeff m:ℂ)*(2*Real.pi:ℂ) := by
  simp_rw [polynomial_kernel]
  rw [intervalIntegral.integral_const_mul, CoefficientIntegral.angular_integral]
  have he : exp ((m:ℂ)*(v:ℂ))*((Real.exp (-v):ℝ):ℂ)^m=1 := by
    rw [Complex.ofReal_exp, ← exp_nat_mul, ← exp_add]
    have hz : (m:ℂ)*(v:ℂ)+(m:ℂ)*((-v:ℝ):ℂ)=0 := by push_cast; ring
    rw [hz, exp_zero]
  calc
    _ = (exp ((m:ℂ)*(v:ℂ))*((Real.exp (-v):ℝ):ℂ)^m)*((p.coeff m:ℂ)*(2*Real.pi:ℂ)) := by ring
    _ = _ := by rw [he, one_mul]

theorem difference_kernel (n m : ℕ) (v θ : ℝ) :
    kernel (difference n) m v θ=kernel (polynomial n) m v θ-kernel EndpointEta.G m v θ := by
  unfold kernel difference
  ring

theorem difference_integral (n m : ℕ) (v : ℝ) (hv : 0 < v) :
    (∫ θ in (0:ℝ)..2*Real.pi, kernel (difference n) m v θ)=
      ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ)-GIntegral m v := by
  have hP := kernel_continuous (polynomial n) m v (polynomial_continuous n v)
  have hG := kernel_continuous EndpointEta.G m v (G_continuous v hv)
  simp_rw [difference_kernel]
  rw [intervalIntegral.integral_sub (hP.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  rw [show (∫ θ in (0:ℝ)..2*Real.pi, kernel (polynomial n) m v θ)=
    ((Borwein.polynomial n).coeff m:ℂ)*(2*Real.pi:ℂ) from polynomial_integral (Borwein.polynomial n) m v]
  rfl

end
end Borwein.EndpointCircleFunctions
