import Borwein.ActualPhaseContinuity

namespace Borwein.CombinedGaussianError
noncomputable section
open Complex Set MeasureTheory CombinedAmplitude AmplitudeTaylor RadialDerivatives
  ActualPhaseTaylor SmallBoxPhaseDecay GaussianMoments

def rate (n τ : ℝ) : ℝ := (39/100)*n*secondDerivative τ
def path (ζ : ℂ) (a : ℕ) (τ t : ℝ) : ℂ := psi ζ a ((τ:ℂ)-(t:ℂ)*I)
def linearCoefficient (ζ : ℂ) (a : ℕ) (τ : ℝ) : ℂ := -I*psiFirst ζ a (τ:ℂ)
def oddTerm (ζ : ℂ) (a : ℕ) (n τ t : ℝ) : ℂ :=
  (psi ζ a (τ:ℂ)*cubicTerm n τ t+linearCoefficient ζ a τ*(t:ℂ))*
    Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)
def remainder (ζ : ℂ) (a : ℕ) (n τ t : ℝ) : ℂ :=
  path ζ a τ t*Complex.exp (saddlePhase n τ t)-
    psi ζ a (τ:ℂ)*Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)-oddTerm ζ a n τ t
def budget2 (τ : ℝ) : ℝ := 4*a2 τ
def budget4 (ζ : ℂ) (a : ℕ) (n τ : ℝ) : ℝ :=
  10*n*W 4 τ*‖psi ζ a (τ:ℂ)‖+(46/3)*n*a1 τ*W 3 τ
def budget6 (ζ : ℂ) (a : ℕ) (n τ : ℝ) : ℝ :=
  (529/72)*n^2*(W 3 τ)^2*‖psi ζ a (τ:ℂ)‖

theorem amplitude_budgets_nonneg (τ : ℝ) : 0 ≤ a1 τ ∧ 0 ≤ a2 τ := by
  unfold a1 a2 AmplitudeBounds.firstBudget AmplitudeBounds.secondBudget
  constructor <;> positivity

theorem budgets_nonneg (ζ : ℂ) (a : ℕ) (n τ : ℝ) (hn : 0 ≤ n) :
    0 ≤ budget2 τ ∧ 0 ≤ budget4 ζ a n τ ∧ 0 ≤ budget6 ζ a n τ := by
  have h1 := (amplitude_budgets_nonneg τ).1
  have h2 := (amplitude_budgets_nonneg τ).2
  have h3 := W_nonneg 3 τ
  have h4 := W_nonneg 4 τ
  unfold budget2 budget4 budget6
  constructor
  · positivity
  constructor <;> positivity

theorem gaussian_exponent_norm (n τ t : ℝ) (hn : 0 ≤ n) :
    ‖Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)‖ ≤ gaussian (rate n τ) t := by
  rw [Complex.norm_exp]
  unfold GaussianPhaseReplacement.exponent gaussian rate
  simp only [Complex.ofReal_re]
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (mul_nonneg hn (secondDerivative_pos τ).le) (sq_nonneg t)
  nlinarith

theorem path_quadratic_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (τ t : ℝ)
    (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖path ζ a τ t-psi ζ a (τ:ℂ)-linearCoefficient ζ a τ*(t:ℂ)‖ ≤ 4*a2 τ*t^2 := by
  have he : path ζ a τ t-psi ζ a (τ:ℂ)-linearCoefficient ζ a τ*(t:ℂ) =
      psi ζ a ((τ:ℂ)-(t:ℂ)*I)-psi ζ a (τ:ℂ)+(t:ℂ)*I*psiFirst ζ a (τ:ℂ) := by
    unfold path linearCoefficient
    ring
  rw [he]
  exact psi_contour_quadratic ζ hζ a τ t hτ ht

theorem pointwise_remainder_bound (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ t : ℝ)
    (hn : 0 ≤ n) (hτ : 0 ≤ τ) (ht : |t| ≤ 2/5) :
    ‖remainder ζ a n τ t‖ ≤
      (budget2 τ*t^2+budget4 ζ a n τ*t^4+budget6 ζ a n τ*t^6)*gaussian (rate n τ) t := by
  let A0 := psi ζ a (τ:ℂ)
  let F := saddlePhase n τ t
  let G := GaussianPhaseReplacement.exponent n (secondDerivative τ) t
  have h0 := mul_le_mul_of_nonneg_left (actual_exponential_remainder n τ t hn hτ ht) (norm_nonneg A0)
  have h1 := mul_le_mul (psi_contour_variation ζ hζ a τ t hτ ht)
    (actual_exponential_difference n τ t hn hτ ht)
    (norm_nonneg (Complex.exp F-Complex.exp G)) (by
      have ha := (amplitude_budgets_nonneg τ).1
      positivity)
  have h2 := mul_le_mul (path_quadratic_bound ζ hζ a τ t hτ ht)
    (gaussian_exponent_norm n τ t hn) (norm_nonneg (Complex.exp G)) (by
      have ha := (amplitude_budgets_nonneg τ).2
      positivity)
  have he := GaussianPhaseReplacement.remainder_decomposition (path ζ a τ t) A0
    (linearCoefficient ζ a τ) F G (cubicTerm n τ t) (t:ℂ)
  have hs : ‖remainder ζ a n τ t‖ ≤
      ‖A0‖*‖Complex.exp F-Complex.exp G-cubicTerm n τ t*Complex.exp G‖+
      ‖path ζ a τ t-A0‖*‖Complex.exp F-Complex.exp G‖+
      ‖path ζ a τ t-A0-linearCoefficient ζ a τ*(t:ℂ)‖*‖Complex.exp G‖ := by
    change ‖path ζ a τ t*Complex.exp F-A0*Complex.exp G-
      (A0*cubicTerm n τ t+linearCoefficient ζ a τ*(t:ℂ))*Complex.exp G‖ ≤ _
    rw [he]
    have hn3 (u v w : ℂ) : ‖u+v+w‖ ≤ ‖u‖+‖v‖+‖w‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    simpa only [norm_mul] using hn3
      (A0*(Complex.exp F-Complex.exp G-cubicTerm n τ t*Complex.exp G))
      ((path ζ a τ t-A0)*(Complex.exp F-Complex.exp G))
      ((path ζ a τ t-A0-linearCoefficient ζ a τ*(t:ℂ))*Complex.exp G)
  have h := hs.trans (add_le_add (add_le_add h0 h1) h2)
  have ht4 : |t|^4=t^4 := by rw [show 4=2*2 by decide,pow_mul,sq_abs,← pow_mul]
  convert! h using 1
  unfold budget2 budget4 budget6 rate A0
  ring_nf
  rw [ht4]
  ring

theorem remainder_continuousOn (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a : ℕ) (n τ h : ℝ)
    (hτ : 0 ≤ τ) (hh : h ≤ 2/5) : ContinuousOn (remainder ζ a n τ) (Icc (-h) h) := by
  have hA := SymmetricGaussian.psi_continuousOn_contour ζ hζ a τ h hτ hh
  have hF := ActualPhaseContinuity.phase_exp_continuousOn n τ h hτ hh
  have hG : Continuous (fun t : ℝ => Complex.exp (GaussianPhaseReplacement.exponent n (secondDerivative τ) t)) := by
    unfold GaussianPhaseReplacement.exponent
    fun_prop
  have hO : Continuous (oddTerm ζ a n τ) := by
    unfold oddTerm cubicTerm GaussianPhaseReplacement.exponent
    fun_prop
  exact ((hA.mul hF).sub (continuousOn_const.mul hG.continuousOn)).sub hO.continuousOn

theorem odd_integral_zero (ζ : ℂ) (a : ℕ) (n τ h : ℝ) :
    (∫ t in -h..h, oddTerm ζ a n τ t) = 0 :=
  actual_odd_correction_integral (psi ζ a (τ:ℂ)) (linearCoefficient ζ a τ) n τ h

end
end Borwein.CombinedGaussianError
