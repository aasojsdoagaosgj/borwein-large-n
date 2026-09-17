import Borwein.ThreeFrequencyCusp

set_option autoImplicit false

namespace Borwein.CuspRectangleBridge
noncomputable section
open scoped ComplexConjugate
open Complex ThreeFrequencyCusp Dilogarithm AngularKernel
  SmoothedResonantMain SmallRadialBaseline

def envelope (l1 l2 l3 : ℝ) : ℝ :=
  max (-l1) (-(3/5)*l1)+max (-l2) (-(3/5:ℝ)^2*l2)/4+
    max (-l3) (-(3/5:ℝ)^3*l3)/9+13/45

theorem pole_conjugate (b : ℕ) (η : ℝ) (z : ℂ) :
    poleIntegral b η (conj z) = poleIntegral b η z := by
  unfold poleIntegral
  apply intervalIntegral.integral_congr
  intro x _
  have he : 1-Complex.exp (-(b:ℂ)*((η:ℂ)+conj z*(x:ℂ))) =
      conj (1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ)))) := by
    rw [map_sub,map_one,← Complex.exp_conj]
    congr 1
    simp
  dsimp only
  rw [he,Complex.norm_conj]

theorem pole_even (η τ t : ℝ) :
    poleIntegral 1 η ((τ:ℂ)-((-t:ℝ):ℂ)*I) = poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) := by
  have he : (τ:ℂ)-((-t:ℝ):ℂ)*I = conj ((τ:ℂ)-(t:ℂ)*I) := by simp
  rw [he,pole_conjugate]

theorem pole_abs (η τ t : ℝ) :
    poleIntegral 1 η ((τ:ℂ)-((|t|:ℝ):ℂ)*I) = poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos (le_of_not_ge ht),pole_even]

theorem lower_sine_transfer (q t l1 l2 l3 : ℝ) (hq0 : 3/5 ≤ q) (hq1 : q ≤ 1)
    (h1 : l1 ≤ Real.sin t) (h2 : l2 ≤ Real.sin (2*t)) (h3 : l3 ≤ Real.sin (3*t)) :
    -(dilog ((q:ℂ)*circle t)).im ≤ envelope l1 l2 l3 := by
  have hq : 0 ≤ q := by linarith
  have hp := polar_upper q t hq hq1
  have hb1 := coefficient_bound q (3/5) (Real.sin t) l1 hq hq1 hq0 h1
  have hb2 := coefficient_bound (q^2) ((3/5)^2) (Real.sin (2*t)) l2 (pow_nonneg hq _)
    (pow_le_one₀ hq hq1) (pow_le_pow_left₀ (by norm_num) hq0 2) h2
  have hb3 := coefficient_bound (q^3) ((3/5)^3) (Real.sin (3*t)) l3 (pow_nonneg hq _)
    (pow_le_one₀ hq hq1) (pow_le_pow_left₀ (by norm_num) hq0 3) h3
  unfold envelope
  linarith

theorem compact_gap_from_bounds (τ t l1 l2 l3 : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2)
    (ht : 0 < t) (h1 : l1 ≤ Real.sin t) (h2 : l2 ≤ Real.sin (2*t)) (h3 : l3 ≤ Real.sin (3*t))
    (hcell : envelope l1 l2 l3 ≤ (9/32:ℝ)*t) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 PositiveCuspCertificate.eta
      ((τ:ℂ)-(t:ℂ)*I) := by
  have hq := damping_bounds τ hτ0 hτ1
  have hs := lower_sine_transfer (Real.exp (-(PositiveCuspCertificate.eta+τ))) t l1 l2 l3 hq.1 hq.2 h1 h2 h3
  have he : Complex.exp (-((PositiveCuspCertificate.eta:ℂ)+((τ:ℂ)-(t:ℂ)*I))) =
      (Real.exp (-(PositiveCuspCertificate.eta+τ)):ℂ)*circle t := by
    rw [circle_eq_exp,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hp := pole_from_imaginary PositiveCuspCertificate.eta τ t (9/32)
    (by norm_num [PositiveCuspCertificate.eta]) hτ0 ht (by norm_num) (by rw [he]; exact hs.trans hcell)
  have hR := small_radial_lower τ hτ1
  linarith

theorem polynomial_from_bounds (n : ℕ) (τ θ l1 l2 l3 : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1)
    (ht : 0 < DirichletCover.localAngle n θ q)
    (h1 : l1 ≤ Real.sin (DirichletCover.localAngle n θ q))
    (h2 : l2 ≤ Real.sin (2*DirichletCover.localAngle n θ q))
    (h3 : l3 ≤ Real.sin (3*DirichletCover.localAngle n θ q))
    (hcell : envelope l1 l2 l3 ≤ (9/32:ℝ)*DirichletCover.localAngle n θ q) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) :=
  SmallAngleIntegral.polynomial_from_gap n τ θ q hn hτ0 (by linarith) hq hb
    (compact_gap_from_bounds τ _ l1 l2 l3 hτ0 hτ1 ht h1 h2 h3 hcell)

end
end Borwein.CuspRectangleBridge
