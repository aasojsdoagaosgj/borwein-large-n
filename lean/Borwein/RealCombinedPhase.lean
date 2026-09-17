import Borwein.SaddleArcConnection

set_option autoImplicit false

namespace Borwein.RealCombinedPhase
noncomputable section
open scoped ComplexConjugate
open MainTermIdentification CombinedAmplitude FiveRootProductExpansion FifthRootLogarithm
  LogFactorDerivatives SaddleArcConnection

theorem lambda_conjugate (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    lambda (conj ξ) (τ:ℂ) = conj (lambda ξ (τ:ℂ)) := by
  rw [lambda_eq_endpoints,lambda_eq_endpoints]
  have hcoeff (j : Fin 4) : coefficients (conj ξ) j = conj (coefficients ξ j) := by
    simp only [coefficients,map_pow]
  have hlog (j : Fin 4) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
      f0 (coefficients (conj ξ) j) (τ:ℂ) x = conj (f0 (coefficients ξ j) (τ:ℂ) x) := by
    rw [hcoeff]
    exact real_log_conjugate _ τ x (coefficient_slit ξ _ hξ hτ (by norm_num) j x hx)
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hlog j 1 (by norm_num),hlog j 0 (by norm_num)]
  simp

theorem amplitude_conjugate (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    amplitude (conj ξ) (τ:ℂ) = conj (amplitude ξ (τ:ℂ)) := by
  rw [amplitude,lambda_conjugate ξ hξ τ hτ,Complex.exp_conj]
  rfl

theorem weighted_pair (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (j : Fin 4) :
    phaseWeight ζ a j.rev*amplitude (coefficients ζ j.rev) (τ:ℂ) =
      conj (phaseWeight ζ a j*amplitude (coefficients ζ j) (τ:ℂ)) := by
  have hc := conjugate_coefficient ζ hζ.pow_eq_one j
  unfold phaseWeight
  rw [hc,amplitude_conjugate _ (coefficient_primitive ζ hζ j) τ hτ]
  simp only [map_mul,map_zpow₀]

theorem psi_real (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    psi ζ a (τ:ℂ) =
      ((2*(phaseWeight ζ a 0*amplitude (coefficients ζ 0) (τ:ℂ)).re+
        2*(phaseWeight ζ a 1*amplitude (coefficients ζ 1) (τ:ℂ)).re : ℝ):ℂ) := by
  have h0 := weighted_pair ζ hζ a τ hτ 0
  have h1 := weighted_pair ζ hζ a τ hτ 1
  change phaseWeight ζ a 3*amplitude (coefficients ζ 3) (τ:ℂ) =
    conj (phaseWeight ζ a 0*amplitude (coefficients ζ 0) (τ:ℂ)) at h0
  change phaseWeight ζ a 2*amplitude (coefficients ζ 2) (τ:ℂ) =
    conj (phaseWeight ζ a 1*amplitude (coefficients ζ 1) (τ:ℂ)) at h1
  unfold psi
  rw [Fin.sum_univ_four,h1,h0]
  apply Complex.ext <;> simp <;> ring

theorem psi_im_zero (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (psi ζ a (τ:ℂ)).im = 0 := by
  rw [psi_real ζ hζ a τ hτ]
  rfl

def angle (ξ : ℂ) (τ : ℝ) : ℝ := (lambda ξ (τ:ℂ)).im

theorem amplitude_angle (ξ : ℂ) (hξ : IsPrimitiveRoot ξ 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    amplitude ξ (τ:ℂ) = Complex.exp ((angle ξ τ:ℂ)*Complex.I) := by
  have hr := lambda_real_re ξ hξ τ hτ
  unfold amplitude
  congr 1
  apply Complex.ext <;> simp [angle,hr]

theorem weighted_real_cos (a : ℕ) (ha : a < 5) (j : Fin 4) (τ : ℝ) (hτ : 0 ≤ τ) :
    (phaseWeight FivePoleCircle.zeta a j*
      amplitude (coefficients FivePoleCircle.zeta j) (τ:ℂ)).re =
      Real.cos (angle (coefficients FivePoleCircle.zeta j) τ-(a:ℝ)*center j) := by
  have hw := angular_phase_weight j a
  rw [Nat.mod_eq_of_lt ha] at hw
  rw [← hw,amplitude_angle _ (coefficient_primitive _ FivePoleCircle.zeta_primitive j) τ hτ,
    ← Complex.exp_add]
  have he : -(a:ℂ)*(center j:ℂ)*Complex.I+
      (angle (coefficients FivePoleCircle.zeta j) τ:ℂ)*Complex.I =
      ((angle (coefficients FivePoleCircle.zeta j) τ-(a:ℝ)*center j:ℝ):ℂ)*Complex.I := by
    push_cast
    ring
  rw [he]
  simp [Complex.exp_re]

theorem psi_two_cosines (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    psi FivePoleCircle.zeta a (τ:ℂ) =
      ((2*Real.cos (angle FivePoleCircle.zeta τ-2*Real.pi*(a:ℝ)/5)+
        2*Real.cos (angle (FivePoleCircle.zeta^2) τ-4*Real.pi*(a:ℝ)/5):ℝ):ℂ) := by
  rw [psi_real _ FivePoleCircle.zeta_primitive a τ hτ,
    weighted_real_cos a ha 0 τ hτ,weighted_real_cos a ha 1 τ hτ]
  congr 1
  norm_num [coefficients,center]
  congr 2 <;> congr 1 <;> ring

end
end Borwein.RealCombinedPhase
