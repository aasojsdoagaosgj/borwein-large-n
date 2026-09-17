import Borwein.ExponentialSegment
import Borwein.GaussianMoments
import Borwein.SymmetricGaussian

namespace Borwein.GaussianPhaseReplacement
noncomputable section
open Complex GaussianMoments

def exponent (n V t : ℝ) : ℂ := (-(n*V*t^2/2):ℝ)

theorem exponent_exp (n V t : ℝ) :
    Complex.exp (exponent n V t) = (gaussian (n*V/2) t:ℂ) := by
  rw [exponent,← Complex.ofReal_exp]
  congr 1
  unfold gaussian
  congr 1
  ring

theorem gaussian_exponent_bound (n V β t : ℝ) (hn : 0 ≤ n) (hV : 0 ≤ V) (hβ : β ≤ 1/2) :
    (exponent n V t).re ≤ -β*n*V*t^2 := by
  have h := mul_le_mul_of_nonneg_right hβ (mul_nonneg (mul_nonneg hn hV) (sq_nonneg t))
  simp only [exponent,Complex.ofReal_re]
  nlinarith

theorem exponential_difference (F : ℂ) (n V W3 β t : ℝ)
    (hn : 0 ≤ n) (hV : 0 ≤ V) (hβ : β ≤ 1/2)
    (hF : F.re ≤ -β*n*V*t^2)
    (hD : ‖F-exponent n V t‖ ≤ (23/6)*n*W3*|t|^3) :
    ‖Complex.exp F-Complex.exp (exponent n V t)‖ ≤
      (23/6)*n*W3*|t|^3*gaussian (β*n*V) t := by
  have h := ExponentialSegment.difference_bound F (exponent n V t) (-β*n*V*t^2) hF
    (gaussian_exponent_bound n V β t hn hV hβ)
  have h' := h.trans (mul_le_mul_of_nonneg_right hD (Real.exp_pos _).le)
  simpa only [gaussian,neg_mul] using h'

theorem cubic_corrected_difference (F C : ℂ) (n V W3 W4 β t : ℝ)
    (hn : 0 ≤ n) (hV : 0 ≤ V) (hβ : β ≤ 1/2)
    (hF : F.re ≤ -β*n*V*t^2)
    (hD : ‖F-exponent n V t‖ ≤ (23/6)*n*W3*|t|^3)
    (hE : ‖F-exponent n V t-C‖ ≤ 10*n*W4*t^4) :
    ‖Complex.exp F-Complex.exp (exponent n V t)-C*Complex.exp (exponent n V t)‖ ≤
      (10*n*W4*t^4+(529/72)*n^2*W3^2*t^6)*gaussian (β*n*V) t := by
  have h := ExponentialSegment.corrected_bound F (exponent n V t) C (-β*n*V*t^2) hF
    (gaussian_exponent_bound n V β t hn hV hβ)
  have hsq := pow_le_pow_left₀ (norm_nonneg (F-exponent n V t)) hD 2
  have hab : |t|^6 = t^6 := by
    rw [show 6=2*3 by decide,pow_mul,sq_abs,← pow_mul]
  have heq : ((23/6)*n*W3*|t|^3)^2/2 = (529/72)*n^2*W3^2*t^6 := by
    ring_nf
    rw [hab]
  have hp : ‖F-exponent n V t-C‖+‖F-exponent n V t‖^2/2 ≤
      10*n*W4*t^4+(529/72)*n^2*W3^2*t^6 := by
    rw [← heq]
    linarith
  have h' := h.trans (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le)
  simpa only [gaussian,neg_mul] using h'

theorem integrand_decomposition (A A0 A1 F G C t : ℂ) :
    A*Complex.exp F-A0*Complex.exp G =
      A0*(Complex.exp F-Complex.exp G-C*Complex.exp G)+
      (A-A0)*(Complex.exp F-Complex.exp G)+
      (A-A0-A1*t)*Complex.exp G+(A0*C+A1*t)*Complex.exp G := by ring

theorem remainder_decomposition (A A0 A1 F G C t : ℂ) :
    A*Complex.exp F-A0*Complex.exp G-(A0*C+A1*t)*Complex.exp G =
      A0*(Complex.exp F-Complex.exp G-C*Complex.exp G)+
      (A-A0)*(Complex.exp F-Complex.exp G)+(A-A0-A1*t)*Complex.exp G := by ring

theorem odd_correction_integral (A0 A1 C3 : ℂ) (n V h : ℝ) :
    (∫ t in -h..h, (A0*(C3*(t:ℂ)^3)+A1*(t:ℂ))*Complex.exp (exponent n V t)) = 0 := by
  simp_rw [exponent_exp]
  have he : (fun t : ℝ => (A0*(C3*(t:ℂ)^3)+A1*(t:ℂ))*(gaussian (n*V/2) t:ℂ)) =
      (fun t : ℝ => (A1*(t:ℂ)+(A0*C3)*(t:ℂ)^3)*(gaussian (n*V/2) t:ℂ)) := by
    funext t
    ring
  rw [he]
  exact SymmetricGaussian.odd_gaussian_integral A1 (A0*C3) (n*V/2) h

end
end Borwein.GaussianPhaseReplacement
