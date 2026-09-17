import Borwein.OuterArcGeometry
import Borwein.CentralMoments

namespace Borwein.OuterMassEnvelope
noncomputable section
open Complex MeasureTheory SaddleArcConnection GapIntegralBounds OuterArcGeometry

def valueNorm (n : ℕ) (τ θ : ℝ) : ℝ :=
  ‖Polynomial.eval₂ (Int.castRingHom ℂ) ((radius n τ:ℂ)*Complex.exp ((θ:ℂ)*I))
    (Borwein.polynomial n)‖

theorem valueNorm_continuous (n : ℕ) (τ : ℝ) : Continuous (valueNorm n τ) := by
  unfold valueNorm
  fun_prop

theorem interval_bound (n : ℕ) (τ a b M : ℝ) (hab : a ≤ b)
    (hb : ∀ θ ∈ Set.Icc a b, valueNorm n τ θ ≤ M) :
    (∫ θ in a..b, valueNorm n τ θ) ≤ (b-a)*M := by
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab ((valueNorm_continuous n τ).intervalIntegrable a b)
    ((continuous_const : Continuous (fun _ : ℝ => M)).intervalIntegrable a b) hb
  simpa [intervalIntegral.integral_const,smul_eq_mul] using hi

theorem mass_bound (n : ℕ) (τ h M : ℝ) (hn : 0 < n) (hh0 : 0 ≤ h) (hh1 : h ≤ 6/5)
    (hb : ∀ θ, region n h θ → valueNorm n τ θ ≤ M) :
    mass n τ h ≤ (2*Real.pi-8*h/(5*(n:ℝ)))*M := by
  have hg := WideGapIntegral.gap_order n h hn hh0 hh1
  have h0 := interval_bound n τ 0 (center 0-h/(5*n)) M hg.1 (fun θ ht => hb θ (Or.inl ht))
  have h1 := interval_bound n τ (center 0+h/(5*n)) (center 1-h/(5*n)) M hg.2.1
    (fun θ ht => hb θ (Or.inr (Or.inl ht)))
  have h2 := interval_bound n τ (center 1+h/(5*n)) (center 2-h/(5*n)) M hg.2.2.1
    (fun θ ht => hb θ (Or.inr (Or.inr (Or.inl ht))))
  have h3 := interval_bound n τ (center 2+h/(5*n)) (center 3-h/(5*n)) M hg.2.2.2.1
    (fun θ ht => hb θ (Or.inr (Or.inr (Or.inr (Or.inl ht)))))
  have h4 := interval_bound n τ (center 3+h/(5*n)) (2*Real.pi) M hg.2.2.2.2
    (fun θ ht => hb θ (Or.inr (Or.inr (Or.inr (Or.inr ht)))))
  have hs := add_le_add (add_le_add (add_le_add (add_le_add h0 h1) h2) h3) h4
  change mass n τ h ≤ _ at hs
  convert! hs using 1
  ring

theorem circle_mass_bound (n : ℕ) (τ h M : ℝ) (hn : 0 < n) (hh0 : 0 ≤ h) (hh1 : h ≤ 6/5)
    (hM : 0 ≤ M) (hb : ∀ θ, region n h θ → valueNorm n τ θ ≤ M) :
    mass n τ h ≤ 2*Real.pi*M := by
  apply (mass_bound n τ h M hn hh0 hh1 hb).trans
  apply mul_le_mul_of_nonneg_right _ hM
  have hd : 0 ≤ 8*h/(5*(n:ℝ)) := by positivity
  linarith

theorem normalization_identity (n m : ℕ) (τ γ : ℝ) (hn : 0 < n) :
    (2*Real.pi*Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-γ)))/
      ((radius n τ)^m*(2*Real.pi)*bulkScale n m τ) =
      5*(n:ℝ)*Real.sqrt (n:ℝ)*Real.sqrt (2*Real.pi*RadialDerivatives.secondDerivative τ)*
        Real.exp (-γ*(n:ℝ)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr : radius n τ ≠ 0 := (Real.exp_pos _).ne'
  have he : Real.exp ((n:ℝ)*PhaseIntegral.radialR τ) ≠ 0 := (Real.exp_pos _).ne'
  have hscale := GaussianNormalization.scale_pos n τ hn0
  have heq : Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-γ)) =
      Real.exp ((n:ℝ)*PhaseIntegral.radialR τ)*Real.exp (-γ*(n:ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs := gaussian_scale_product n τ hn
  rw [heq,bulkScale]
  field_simp
  nlinarith [hs]

theorem gaussian_prefactor (τ : ℝ) : 5*Real.sqrt (2*Real.pi*RadialDerivatives.secondDerivative τ) ≤ 15 := by
  have hV := CentralMoments.variance_integral_le τ
  have hVp := RadialDerivatives.secondDerivative_pos τ
  have hπ := Real.pi_lt_d20
  have hx : 2*Real.pi*RadialDerivatives.secondDerivative τ ≤ 9 := by
    nlinarith [mul_le_mul_of_nonneg_left hV (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  have hs : Real.sqrt (2*Real.pi*RadialDerivatives.secondDerivative τ) ≤ 3 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num; exact hx⟩
  linarith

theorem normalized_mass_bound (n m : ℕ) (τ γ : ℝ) (hn : 0 < n)
    (hb : ∀ θ, region n (6/5) θ →
      valueNorm n τ θ ≤ Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-γ))) :
    mass n τ (6/5)/((radius n τ)^m*(2*Real.pi)*bulkScale n m τ) ≤
      15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-γ*(n:ℝ)) := by
  have hden : 0 < (radius n τ)^m*(2*Real.pi)*bulkScale n m τ := by
    positivity [bulkScale_pos n m τ hn,Real.exp_pos (-τ/(5*n))]
  have hm := div_le_div_of_nonneg_right (circle_mass_bound n τ (6/5)
    (Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-γ))) hn (by norm_num) (by norm_num)
    (Real.exp_pos _).le hb) hden.le
  rw [normalization_identity n m τ γ hn] at hm
  apply hm.trans
  have hs := mul_le_mul_of_nonneg_right (gaussian_prefactor τ)
    (by positivity : 0 ≤ (n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-γ*(n:ℝ)))
  convert! hs using 1 <;> ring

theorem coefficient_error (n m : ℕ) (τ N γ : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2))
    (hb : ∀ θ, region n (6/5) θ →
      valueNorm n τ θ ≤ Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-γ))) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
      FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ (2/5) N+
      MiddlePolynomialIntegral.error n τ+
      15*(n:ℝ)*Real.sqrt (n:ℝ)*Real.exp (-γ*(n:ℝ)) := by
  have hnNat : 0 < n := by exact_mod_cast hN.trans_le hn
  exact (WideGapIntegral.coefficient_error_with_outer_mass n m τ N hN hn hτ0 hτ1 hs).trans
    (add_le_add le_rfl (normalized_mass_bound n m τ γ hnNat hb))

end
end Borwein.OuterMassEnvelope
