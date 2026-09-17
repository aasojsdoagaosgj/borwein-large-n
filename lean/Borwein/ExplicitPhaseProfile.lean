import Borwein.ArctangentPhase

set_option autoImplicit false

namespace Borwein.ExplicitPhaseProfile
noncomputable section
open LogPhaseCoordinates ArctangentPhase AngularKernel

def parameter (τ : ℝ) : ℝ := (1-Real.exp (-τ))/(1+Real.exp (-τ))
def alpha (τ : ℝ) : ℝ := Real.arctan (parameter τ*(Real.cos (Real.pi/5)/Real.sin (Real.pi/5)))
def beta (τ : ℝ) : ℝ := Real.arctan (parameter τ*(Real.cos (2*Real.pi/5)/Real.sin (2*Real.pi/5)))
def phase (a : ℕ) (τ : ℝ) : ℝ :=
  4*Real.cos (3*Real.pi*(a:ℝ)/5+(alpha τ+2*beta τ)/5)*
    Real.cos (-Real.pi*(a:ℝ)/5+(2*alpha τ-beta τ)/5)

theorem half_angle_ratio (t : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi) :
    (circle (2*t)).im/(1-(circle (2*t)).re) = Real.cos t/Real.sin t := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht0 ht1
  simp only [circle,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,
    Complex.I_re,Complex.ofReal_re,mul_one,zero_mul,mul_zero,zero_add,add_zero,
    Complex.add_re,Complex.mul_re,sub_zero]
  rw [Real.sin_two_mul,Real.cos_two_mul_eq_one_sub]
  field_simp
  ring

theorem circle_argumentShift (t τ : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi/2) (hτ : 0 ≤ τ) :
    argumentShift (circle (2*t)) τ =
      Real.arctan (parameter τ*(Real.cos t/Real.sin t)) := by
  have hs := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [Real.pi_pos])
  have hr : (circle (2*t)).re < 1 := by
    simp only [circle,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_im,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
    rw [Real.cos_two_mul_eq_one_sub]
    nlinarith [sq_pos_of_pos hs]
  have hi : 0 ≤ (circle (2*t)).im := by
    simp only [circle,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_im,
      Complex.I_re,Complex.ofReal_re,mul_one,zero_mul,mul_zero,zero_add,add_zero]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith,by linarith⟩
  have hu : (circle (2*t)).re^2+(circle (2*t)).im^2 = 1 := by
    simp only [circle,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      mul_one,sub_zero,zero_add,add_zero]
    nlinarith [Real.sin_sq_add_cos_sq (2*t)]
  rw [argumentShift_arctan _ hu hr hi τ hτ,
    half_angle_ratio t ht0 (by linarith [Real.pi_pos])]
  rfl

theorem first_argument (τ : ℝ) (hτ : 0 ≤ τ) :
    argumentShift FivePoleCircle.zeta τ = alpha τ := by
  have hξ : FivePoleCircle.zeta = circle (2*(Real.pi/5)) := by
    unfold FivePoleCircle.zeta
    congr 1
    ring
  rw [hξ,circle_argumentShift _ τ (by positivity) (by linarith [Real.pi_pos]) hτ]
  rfl

theorem second_argument (τ : ℝ) (hτ : 0 ≤ τ) :
    argumentShift (FivePoleCircle.zeta^2) τ = beta τ := by
  have hξ : FivePoleCircle.zeta^2 = circle (2*(2*Real.pi/5)) := by
    rw [FivePoleCircle.zeta,circle_pow]
    congr 1
  rw [hξ,circle_argumentShift _ τ (by positivity) (by linarith [Real.pi_pos]) hτ]
  rfl

theorem psi_eq_profile (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    CombinedAmplitude.psi FivePoleCircle.zeta a (τ:ℂ) = (phase a τ:ℂ) := by
  rw [psi_cosine_product a ha τ hτ]
  simp only [U,Vangle,first_argument τ hτ,second_argument τ hτ,phase]

theorem profile_norm (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖CombinedAmplitude.psi FivePoleCircle.zeta a (τ:ℂ)‖ = |phase a τ| := by
  rw [psi_eq_profile a ha τ hτ,Complex.norm_real,Real.norm_eq_abs]

theorem parameter_range (τ : ℝ) (hτ : 0 ≤ τ) :
    0 ≤ parameter τ ∧ parameter τ < 1 := by
  have he := Real.exp_pos (-τ)
  have he1 : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd : 0 < 1+Real.exp (-τ) := by positivity
  unfold parameter
  constructor
  · exact div_nonneg (by linarith) hd.le
  · exact (div_lt_one hd).mpr (by linarith)

end
end Borwein.ExplicitPhaseProfile
