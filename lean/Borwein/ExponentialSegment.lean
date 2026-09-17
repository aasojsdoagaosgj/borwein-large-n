import Borwein.SecondOrderSegment
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Borwein.ExponentialSegment
noncomputable section
open Complex Set

def line (F G : ℂ) (t : ℝ) : ℂ := G+(t:ℂ)*(F-G)

theorem line_zero (F G : ℂ) : line F G 0 = G := by simp [line]
theorem line_one (F G : ℂ) : line F G 1 = F := by simp [line]

theorem line_real_bound (F G : ℂ) (B : ℝ) (hF : F.re ≤ B) (hG : G.re ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : (line F G t).re ≤ B := by
  have h1 := mul_le_mul_of_nonneg_left hF ht.1
  have h2 := mul_le_mul_of_nonneg_left hG (sub_nonneg.mpr ht.2)
  simp only [line,Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,Complex.sub_re]
  nlinarith

theorem line_exp_deriv (F G : ℂ) (t : ℝ) :
    HasDerivAt (fun t => Complex.exp (line F G t)) ((F-G)*Complex.exp (line F G t)) t := by
  have hi : HasDerivAt (fun t : ℝ => (t:ℂ)) 1 t := by
    convert! Complex.ofRealCLM.hasDerivAt (x := t) using 1
  unfold line
  convert! (((hi.mul_const (F-G)).const_add G).cexp) using 1 <;> ring

theorem line_exp_second_deriv (F G : ℂ) (t : ℝ) :
    HasDerivAt (fun t => (F-G)*Complex.exp (line F G t))
      ((F-G)^2*Complex.exp (line F G t)) t := by
  convert! (line_exp_deriv F G t).const_mul (F-G) using 1 <;> ring

theorem line_exp_norm_bound (F G : ℂ) (B : ℝ) (hF : F.re ≤ B) (hG : G.re ≤ B)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : ‖Complex.exp (line F G t)‖ ≤ Real.exp B := by
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr (line_real_bound F G B hF hG t ht)

theorem difference_bound (F G : ℂ) (B : ℝ) (hF : F.re ≤ B) (hG : G.re ≤ B) :
    ‖Complex.exp F-Complex.exp G‖ ≤ ‖F-G‖*Real.exp B := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (line_exp_deriv F G t).hasDerivWithinAt)
    (fun t ht => show ‖(F-G)*Complex.exp (line F G t)‖ ≤ ‖F-G‖*Real.exp B from by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (line_exp_norm_bound F G B hF hG t ⟨ht.1,ht.2.le⟩) (norm_nonneg _))
  simpa only [line_one,line_zero] using h

theorem quadratic_bound (F G : ℂ) (B : ℝ) (hF : F.re ≤ B) (hG : G.re ≤ B) :
    ‖Complex.exp F-Complex.exp G-(F-G)*Complex.exp G‖ ≤ ‖F-G‖^2/2*Real.exp B := by
  have h := SecondOrderSegment.remainder_bound
    (fun t => Complex.exp (line F G t)) (fun t => (F-G)*Complex.exp (line F G t))
    (fun t => (F-G)^2*Complex.exp (line F G t)) (‖F-G‖^2*Real.exp B)
    (fun t _ => line_exp_deriv F G t) (fun t _ => line_exp_second_deriv F G t)
    (by unfold line; fun_prop)
    (fun t ht => by
      rw [norm_mul,norm_pow]
      exact mul_le_mul_of_nonneg_left (line_exp_norm_bound F G B hF hG t ht) (sq_nonneg _))
  simp only [line_one,line_zero] at h
  convert! h using 1 <;> ring

theorem corrected_bound (F G C : ℂ) (B : ℝ) (hF : F.re ≤ B) (hG : G.re ≤ B) :
    ‖Complex.exp F-Complex.exp G-C*Complex.exp G‖ ≤
      (‖F-G-C‖+‖F-G‖^2/2)*Real.exp B := by
  have he : Complex.exp F-Complex.exp G-C*Complex.exp G =
      (Complex.exp F-Complex.exp G-(F-G)*Complex.exp G)+(F-G-C)*Complex.exp G := by ring
  rw [he]
  have h1 := quadratic_bound F G B hF hG
  have h2 : ‖(F-G-C)*Complex.exp G‖ ≤ ‖F-G-C‖*Real.exp B := by
    rw [norm_mul,Complex.norm_exp]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hG) (norm_nonneg _)
  have h := (norm_add_le _ _).trans (add_le_add h1 h2)
  convert! h using 1 <;> ring

end
end Borwein.ExponentialSegment
