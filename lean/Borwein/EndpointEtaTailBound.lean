import Borwein.EndpointTailGlobalLog
import Borwein.EndpointWeakPolynomial

set_option autoImplicit false

namespace Borwein.EndpointEtaTailBound
noncomputable section
open Complex FivePoleCircle EndpointTailGlobalLog EndpointWeakPolynomial

theorem root_radius (j : Fin 4) (v y : ℝ) :
    ‖zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I))‖=Real.exp (-v) := by
  rw [norm_mul, FiveRootProductExpansion.root_norm _ (EndpointTailRootSeries.actual_root_fifth j), one_mul, Complex.norm_exp]
  simp

theorem circle_tail_bound (n : ℕ) (v θ : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖EndpointFiniteConnection.tail n ((Real.exp (-v):ℂ)*AngularKernel.circle θ)-1‖ ≤
      (radialX n v/v)*Real.exp (radialX n v/v) := by
  apply endpoint_tail_bound n _ v hn hv hV hτ
  rw [norm_mul, AngularKernel.circle_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem root_tail_bound (n : ℕ) (j : Fin 4) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))-1‖ ≤
      (radialX n v/v)*Real.exp (radialX n v/v) :=
  endpoint_tail_bound n _ v hn hv hV hτ (root_radius j v y)

/-- The previous eta-remainder theorem's tail-factor hypothesis is now discharged. -/
theorem eta_remainder_bound (a n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖etaRemainder a n ((v:ℂ)+(y:ℂ)*I)‖ ≤
      40*‖EndpointRootAsymptotic.main ((v:ℂ)+(y:ℂ)*I)‖*Real.exp (-1/v)*
        ((radialX n v/v)*Real.exp (radialX n v/v)) := by
  apply etaRemainder_bound a n v y _ hv hV hy
  · unfold radialX
    positivity
  · exact fun j => root_tail_bound n j v y hn hv hV hτ

end
end Borwein.EndpointEtaTailBound
