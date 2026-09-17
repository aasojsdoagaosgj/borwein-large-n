import Borwein.ShiftedDilogarithm
import Borwein.SmallAngleIntegral

set_option autoImplicit false

namespace Borwein.LargeAnglePole
noncomputable section
open Complex ShiftedDilogarithm SmoothedResonantMain SmallRadialBaseline SmallAngleIntegral

theorem pole_large_angle (η τ t : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ) (ht : 6 ≤ |t|) :
    4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) ≤ 11/10 := by
  have hn : 6 ≤ ‖(τ:ℂ)-(t:ℂ)*I‖ := by
    have h := Complex.abs_im_le_norm ((τ:ℂ)-(t:ℂ)*I)
    simp only [Complex.sub_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_sub,abs_neg] at h
    exact ht.trans h
  have hpos : 0 < ‖(τ:ℂ)-(t:ℂ)*I‖ := by linarith
  have h := pole_norm_upper η ((τ:ℂ)-(t:ℂ)*I) hη (by simpa using hτ) (norm_pos_iff.mp hpos)
  have hpi : Real.pi^2/6 ≤ (33/20:ℝ) := by nlinarith [Real.pi_lt_d4,Real.pi_pos]
  have hd : (Real.pi^2/6)/‖(τ:ℂ)-(t:ℂ)*I‖ ≤ 11/40 := by
    apply (div_le_iff₀ hpos).mpr
    linarith
  linarith

theorem large_gap (η τ t : ℝ) (hη : 0 < η) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2) (ht : 6 ≤ |t|) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 η ((τ:ℂ)-(t:ℂ)*I) := by
  have hR := small_radial_lower τ hτ1
  have hH := pole_large_angle η τ t hη hτ0 ht
  linarith

theorem polynomial_large_angle (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1)
    (ht : 6 ≤ |DirichletCover.localAngle n θ q|) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) :=
  polynomial_from_gap n τ θ q hn hτ0 (by linarith) hq hb
    (large_gap _ τ _ (by norm_num [PositiveCuspCertificate.eta]) hτ0 hτ1 ht)

theorem covered_region (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1)
    (hregion : 1/2 ≤ τ ∨ |DirichletCover.localAngle n θ q| ≤ 2 ∨
      6 ≤ |DirichletCover.localAngle n θ q|) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) := by
  by_cases hτ : 1/2 ≤ τ
  · exact DenominatorOnePositiveCertificate.polynomial_decay n τ θ q hn hτ hτ1 hq hb
  rcases hregion with h | h | h
  · exact False.elim (hτ h)
  · exact polynomial_small_angle n τ θ q hn hτ0 (by linarith) hq hb h
  · exact polynomial_large_angle n τ θ q hn hτ0 (by linarith) hq hb h

end
end Borwein.LargeAnglePole
