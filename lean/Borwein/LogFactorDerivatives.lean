import Borwein.EulerMaclaurin
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace Borwein.LogFactorDerivatives
noncomputable section
open MeasureTheory Set

def w (c z : ℂ) (x : ℝ) : ℂ := c*Complex.exp (-z*(x:ℂ))
def kernel (c z : ℂ) (x : ℝ) : ℂ := 1-w c z x
def f0 (c z : ℂ) (x : ℝ) : ℂ := Complex.log (kernel c z x)
def f1 (c z : ℂ) (x : ℝ) : ℂ := z*w c z x/kernel c z x
def f2 (c z : ℂ) (x : ℝ) : ℂ := -(z^2)*w c z x/(kernel c z x)^2
def f3 (c z : ℂ) (x : ℝ) : ℂ := z^3*w c z x*(1+w c z x)/(kernel c z x)^3

theorem w_deriv (c z : ℂ) (x : ℝ) : HasDerivAt (w c z) (-z*w c z x) x := by
  have hi : HasDerivAt (fun x : ℝ => (x:ℂ)) 1 x := by
    convert! Complex.ofRealCLM.hasDerivAt (x := x) using 1
  unfold w
  convert! ((hi.const_mul (-z)).cexp).const_mul c using 1 <;> ring

theorem kernel_deriv (c z : ℂ) (x : ℝ) : HasDerivAt (kernel c z) (z*w c z x) x := by
  unfold kernel
  convert! (w_deriv c z x).const_sub 1 using 1 <;> ring

theorem log_deriv (c z : ℂ) (x : ℝ) (hs : kernel c z x ∈ Complex.slitPlane) :
    HasDerivAt (f0 c z) (f1 c z x) x := by
  unfold f0 f1
  exact (kernel_deriv c z x).clog_real hs

theorem first_deriv (c z : ℂ) (x : ℝ) (hk : kernel c z x ≠ 0) :
    HasDerivAt (f1 c z) (f2 c z x) x := by
  have h := ((w_deriv c z x).const_mul z).div (kernel_deriv c z x) hk
  unfold f1 f2
  convert! h using 1
  simp only [kernel] at hk ⊢
  field_simp
  ring

theorem second_deriv (c z : ℂ) (x : ℝ) (hk : kernel c z x ≠ 0) :
    HasDerivAt (f2 c z) (f3 c z x) x := by
  have h := ((w_deriv c z x).const_mul (-(z^2))).div
    ((kernel_deriv c z x).pow 2) (pow_ne_zero 2 hk)
  unfold f2 f3
  convert! h using 1
  simp only [Pi.pow_apply,kernel] at hk ⊢
  norm_num
  field_simp
  ring

theorem w_norm_le_one (c z : ℂ) (x : ℝ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (hx : 0 ≤ x) :
    ‖w c z x‖ ≤ 1 := by
  have he : Real.exp (-z*(x:ℂ)).re ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hx
  simpa [w,norm_mul,Complex.norm_exp] using mul_le_mul hc he (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 1)

theorem slit_of_norm_le_one (v : ℂ) (hv : ‖v‖ ≤ 1) (hk : 1-v ≠ 0) :
    1-v ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  by_cases hi : (1-v).im = 0
  · left
    have hr : v.re ≤ 1 := (Complex.re_le_norm v).trans hv
    have hne : v.re ≠ 1 := by
      intro he
      apply hk
      apply Complex.ext <;> simp_all
    simpa using sub_pos.mpr (lt_of_le_of_ne hr hne)
  · exact Or.inr hi

theorem third_continuousOn (c z : ℂ) (s : Set ℝ) (hk : ∀ x ∈ s, kernel c z x ≠ 0) :
    ContinuousOn (f3 c z) s := by
  unfold f3
  apply ContinuousOn.div
  · unfold w; fun_prop
  · unfold kernel w; fun_prop
  · intro x hx
    exact pow_ne_zero 3 (hk x hx)

end
end Borwein.LogFactorDerivatives
