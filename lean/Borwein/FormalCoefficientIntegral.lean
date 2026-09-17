import Borwein.FormalSeriesValue
import Borwein.EndpointOuterTransfer
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace Borwein.FormalCoefficientIntegral
noncomputable section
open Complex PowerSeries MeasureTheory FormalSeriesValue EndpointCircleKernel EndpointCircleFunctions

def summand (f : ℤ⟦X⟧) (m : ℕ) (v : ℝ) (n : ℕ) : ℝ → ℂ :=
  EndpointCircleKernel.kernel (fun q => term f q n) m v

theorem summand_continuous (f : ℤ⟦X⟧) (m n : ℕ) (v : ℝ) :
    Continuous (summand f m v n) := by
  apply kernel_continuous
  exact continuous_const.mul ((point_continuous v).pow n)

theorem summand_norm (f : ℤ⟦X⟧) (m n : ℕ) (v θ : ℝ) :
    ‖summand f m v n θ‖=‖term f ((Real.exp (-v):ℝ):ℂ) n‖*Real.exp ((m:ℝ)*v) := by
  rw [summand, EndpointOuterTransfer.kernel_norm]
  simp only [term, norm_mul, Complex.norm_pow, point_norm, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem summand_integral (f : ℤ⟦X⟧) (m n : ℕ) (v : ℝ) :
    (∫ θ in (0:ℝ)..2*Real.pi, summand f m v n θ)=
      if n=m then ((coeff m f:ℤ):ℂ)*(2*Real.pi:ℂ) else 0 := by
  have he : summand f m v n=EndpointCircleKernel.kernel
      (fun q => Polynomial.eval₂ (Int.castRingHom ℂ) q (Polynomial.monomial n (coeff n f))) m v := by
    funext θ
    simp only [summand, EndpointCircleKernel.kernel, Polynomial.eval₂_monomial, Int.coe_castRingHom, term]
  rw [he, polynomial_integral]
  by_cases hn : n=m
  · subst n; simp
  · simp [Polynomial.coeff_monomial, hn, Ne.symm hn]

/-- Absolute coefficient evaluation justifies the coefficient contour integral. -/
theorem integral_value (f : ℤ⟦X⟧) (F : ℂ → ℂ)
    (hF : ∀ q : ℂ, ‖q‖ < 1 → Converges f q (F q)) (m : ℕ) (v : ℝ) (hv : 0 < v) :
    (∫ θ in (0:ℝ)..2*Real.pi, EndpointCircleKernel.kernel F m v θ)=((coeff m f:ℤ):ℂ)*(2*Real.pi:ℂ) := by
  have hr : ‖((Real.exp (-v):ℝ):ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs := ((hF ((Real.exp (-v):ℝ):ℂ) hr).1).mul_right (Real.exp ((m:ℝ)*v))
  have hp (θ : ℝ) : HasSum (fun n : ℕ => summand f m v n θ) (EndpointCircleKernel.kernel F m v θ) := by
    have hq : ‖point v θ‖ < 1 := by
      rw [point_norm]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    exact (hF (point v θ) hq).2.mul_right (exp ((m:ℂ)*((v:ℂ)-(θ:ℂ)*I)))
  have hi : HasSum (fun n : ℕ => ∫ θ in (0:ℝ)..2*Real.pi, summand f m v n θ)
      (∫ θ in (0:ℝ)..2*Real.pi, EndpointCircleKernel.kernel F m v θ) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n (_ : ℝ) => ‖term f ((Real.exp (-v):ℝ):ℂ) n‖*Real.exp ((m:ℝ)*v))
      (fun n => (summand_continuous f m n v).aestronglyMeasurable)
    · intro n
      exact ae_of_all _ (fun θ _ => (summand_norm f m n v θ).le)
    · exact ae_of_all _ (fun _ _ => hs)
    · exact intervalIntegrable_const
    · exact ae_of_all _ (fun θ _ => hp θ)
  simp_rw [summand_integral] at hi
  exact (hi.unique (hasSum_ite_eq m (((coeff m f:ℤ):ℂ)*(2*Real.pi:ℂ))))

end
end Borwein.FormalCoefficientIntegral
