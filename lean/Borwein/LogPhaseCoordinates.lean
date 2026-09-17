import Borwein.RealCombinedPhase

set_option autoImplicit false

namespace Borwein.LogPhaseCoordinates
noncomputable section
open scoped ComplexConjugate
open MainTermIdentification CombinedAmplitude FiveRootProductExpansion FifthRootLogarithm
  LogFactorDerivatives RealCombinedPhase

def logShift (ξ : ℂ) (τ : ℝ) : ℂ :=
  Complex.log (1-ξ*Complex.exp (-(τ:ℂ)))-Complex.log (1-ξ)

def argumentShift (ξ : ℂ) (τ : ℝ) : ℝ := (logShift ξ τ).im

theorem logShift_endpoints (ξ : ℂ) (τ : ℝ) :
    logShift ξ τ = f0 ξ (τ:ℂ) 1-f0 ξ (τ:ℂ) 0 := by
  simp [logShift,f0,kernel,w]

theorem logShift_conjugate (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    logShift (conj ξ) τ = conj (logShift ξ τ) := by
  have hs (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
      kernel ξ (τ:ℂ) x ∈ Complex.slitPlane := by
    simpa [coefficients] using coefficient_slit ξ _ hξ hτ (by norm_num) 0 x hx
  rw [logShift_endpoints,logShift_endpoints,
    real_log_conjugate ξ τ 1 (hs 1 (by norm_num)),
    real_log_conjugate ξ τ 0 (hs 0 (by norm_num)),map_sub]

theorem argumentShift_conjugate (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    argumentShift (conj ξ) τ = -argumentShift ξ τ := by
  simp only [argumentShift,logShift_conjugate ξ hξ τ hτ,Complex.conj_im]

theorem angle_formula (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    angle ξ τ = -(3*argumentShift ξ τ+argumentShift (ξ^2) τ)/5 := by
  have h0 : logShift (ξ^4) τ = conj (logShift ξ τ) := by
    rw [← conjugate_root ξ hξ.pow_eq_one]
    exact logShift_conjugate ξ hξ τ hτ
  have h1 : logShift (ξ^3) τ = conj (logShift (ξ^2) τ) := by
    have hc := conjugate_coefficient ξ hξ.pow_eq_one 1
    change ξ^3 = conj (ξ^2) at hc
    rw [hc]
    exact logShift_conjugate _ (by simpa [coefficients] using coefficient_primitive ξ hξ 1) τ hτ
  have he : lambda ξ (τ:ℂ) = ∑ j : Fin 4,
      PeanoQuadrature.B1 (shift j) • logShift (coefficients ξ j) τ := rfl
  unfold angle
  rw [he]
  norm_num [Fin.sum_univ_four,shift,PeanoQuadrature.B1,coefficients]
  rw [h0,h1]
  simp only [Complex.add_im,Complex.smul_im,Complex.conj_im,argumentShift]
  ring

theorem square_angle (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    angle (ξ^2) τ = (argumentShift ξ τ-3*argumentShift (ξ^2) τ)/5 := by
  have hp : IsPrimitiveRoot (ξ^2) 5 := by
    simpa [coefficients] using coefficient_primitive ξ hξ 1
  rw [angle_formula (ξ^2) hp τ hτ,← pow_mul]
  norm_num only [Nat.reduceMul]
  rw [← conjugate_root ξ hξ.pow_eq_one,argumentShift_conjugate ξ hξ τ hτ]
  ring

def U (τ : ℝ) : ℝ :=
  (argumentShift FivePoleCircle.zeta τ+2*argumentShift (FivePoleCircle.zeta^2) τ)/5

def Vangle (τ : ℝ) : ℝ :=
  (2*argumentShift FivePoleCircle.zeta τ-argumentShift (FivePoleCircle.zeta^2) τ)/5

theorem psi_cosine_product (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    psi FivePoleCircle.zeta a (τ:ℂ) =
      ((4*Real.cos (3*Real.pi*(a:ℝ)/5+U τ)*
        Real.cos (-Real.pi*(a:ℝ)/5+Vangle τ):ℝ):ℂ) := by
  rw [psi_two_cosines a ha τ hτ,
    angle_formula _ FivePoleCircle.zeta_primitive τ hτ,
    square_angle _ FivePoleCircle.zeta_primitive τ hτ]
  congr 1
  let α := argumentShift FivePoleCircle.zeta τ
  let β := argumentShift (FivePoleCircle.zeta^2) τ
  change 2*Real.cos (-(3*α+β)/5-2*Real.pi*(a:ℝ)/5)+
    2*Real.cos ((α-3*β)/5-4*Real.pi*(a:ℝ)/5) = _
  rw [show 2*Real.cos (-(3*α+β)/5-2*Real.pi*(a:ℝ)/5)+
      2*Real.cos ((α-3*β)/5-4*Real.pi*(a:ℝ)/5) =
      2*(Real.cos (-(3*α+β)/5-2*Real.pi*(a:ℝ)/5)+
        Real.cos ((α-3*β)/5-4*Real.pi*(a:ℝ)/5)) by ring,
    Real.cos_add_cos]
  have hsum : (-(3*α+β)/5-2*Real.pi*(a:ℝ)/5+
      ((α-3*β)/5-4*Real.pi*(a:ℝ)/5))/2 = -(3*Real.pi*(a:ℝ)/5+U τ) := by
    dsimp [α,β,U]
    ring
  have hdiff : (-(3*α+β)/5-2*Real.pi*(a:ℝ)/5-
      ((α-3*β)/5-4*Real.pi*(a:ℝ)/5))/2 = -(-Real.pi*(a:ℝ)/5+Vangle τ) := by
    dsimp [α,β,Vangle]
    ring
  rw [hsum,hdiff,Real.cos_neg,Real.cos_neg]
  ring

end
end Borwein.LogPhaseCoordinates
