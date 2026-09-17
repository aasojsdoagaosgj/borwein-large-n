import Borwein.EndpointAmplitudeBudget

set_option autoImplicit false

namespace Borwein.EndpointLocalAmplitudeIntegral
noncomputable section
open Complex Set MeasureTheory EndpointGaussianIntegral EndpointGaussianBudget
  EndpointAbsoluteIntegral EndpointAmplitudeBudget EndpointAmplitudeContinuity EndpointTaylor

def integral (n : ℕ) (v : ℝ) (ε : ℝ → ℂ) : ℂ :=
  ∫ y in -(width v)..width v, exp (phase n v y)*adjusted ε y

theorem amplitude_difference (n : ℕ) (v X : ℝ) (ε : ℝ → ℂ)
    (hn : 0 < n) (hv : 0 < v) (hX : 0 ≤ X) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v)
    (hc : Continuous ε)
    (hb : ∀ y ∈ Icc (-(width v)) (width v), ‖ε y‖ ≤ 8*X+25*‖EndpointPhaseAtoms.coordinate v y‖) :
    ‖integral n v ε-localIntegral n v‖ ≤ (15*X+60*v)*normalizer n v := by
  have hP := (phase_continuous n v hn hv).cexp
  have hA := adjusted_continuous ε hc
  have hPA : Continuous (fun y => exp (phase n v y)*adjusted ε y) := hP.mul hA
  have he : integral n v ε-localIntegral n v =
      ∫ y in -(width v)..width v, exp (phase n v y)*(adjusted ε y-1) := by
    rw [integral, localIntegral, ← intervalIntegral.integral_sub
      (hPA.intervalIntegrable _ _) (hP.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [he]
  have hh := weighted_integral_error n v (8*X+32*v) (fun y => adjusted ε y-1) hn hv hτ
    (by positivity) (hA.sub continuous_const).continuousOn
    (fun y hy => adjusted_error ε X v y hv (abs_le.mpr ⟨hy.1, hy.2⟩) (hb y hy))
  apply hh.trans
  have hJ := normalizer_pos n v hn hv
  nlinarith

theorem normalized_bound (n : ℕ) (v X : ℝ) (ε : ℝ → ℂ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hX : 0 ≤ X)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) (hc : Continuous ε)
    (hb : ∀ y ∈ Icc (-(width v)) (width v), ‖ε y‖ ≤ 8*X+25*‖EndpointPhaseAtoms.coordinate v y‖) :
    ‖integral n v ε/(normalizer n v:ℂ)-1‖ ≤ 15*Real.sqrt v+15*X+60*v := by
  have hJ := normalizer_pos n v hn hv
  have ha := amplitude_difference n v X ε hn hv hX hτ hc hb
  have hd : ‖(integral n v ε-localIntegral n v)/(normalizer n v:ℂ)‖ ≤ 15*X+60*v := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hJ.le]
    exact (div_le_iff₀ hJ).mpr ha
  have he : integral n v ε/(normalizer n v:ℂ)-1 =
      (localIntegral n v/(normalizer n v:ℂ)-1)+(integral n v ε-localIntegral n v)/(normalizer n v:ℂ) := by ring
  rw [he]
  exact (norm_add_le _ _).trans (by
    have hg := gaussian_budget n v hn hv hV hτ
    linarith)

theorem strong_normalized_bound (a : Fin 3) (n : ℕ) (v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖integral n v (strongError a n v)/(normalizer n v:ℂ)-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+60*v := by
  apply normalized_bound n v _ _ hn hv hV (Real.exp_pos _).le hτ
    (strongError_continuous a n v hn hv)
  intro y hy
  exact strong_error_bound a n v y hn hv hV (abs_le.mpr ⟨hy.1, hy.2⟩) hτ

theorem weak_normalized_bound (a n : ℕ) (ha : a=3 ∨ a=4) (v : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖integral n v (weakError a n v)/(normalizer n v:ℂ)-1‖ ≤
      15*Real.sqrt v+15*EndpointTailGlobalLog.radialX n v+60*v := by
  apply normalized_bound n v _ _ hn hv hV (Real.exp_pos _).le hτ
    (weakError_continuous a n v hn hv)
  intro y hy
  exact weak_error_bound a n ha v y hn hv hV (abs_le.mpr ⟨hy.1, hy.2⟩) hτ

end
end Borwein.EndpointLocalAmplitudeIntegral
