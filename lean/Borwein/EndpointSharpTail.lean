import Borwein.EndpointTailKernel

set_option autoImplicit false

namespace Borwein.EndpointSharpTail
noncomputable section
open Complex EndpointTailRootSeries EndpointTailKernel WedgeRootKernel

def x (n : ℕ) (w : ℂ) : ℂ := exp (-((5*n:ℕ):ℂ)*w)
def mainTerm (n : ℕ) (ξ w : ℂ) (l : ℕ) : ℂ :=
  x n w^(l+1)/((l+1:ℕ):ℂ)*principal (ξ^(l+1)) (((l+1:ℕ):ℂ)*w)
def errorTerm (n : ℕ) (ξ w : ℂ) (l : ℕ) : ℂ := rootTerm n ξ w l-mainTerm n ξ w l

theorem power_fifth (ξ : ℂ) (hξ : ξ^5=1) (k : ℕ) : (ξ^k)^5=1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hξ, one_pow]

theorem inverse_pole (ξ z : ℂ) (hξ : ξ ≠ 0) :
    1/(ξ⁻¹*exp z-1) = pole ξ z := by
  have he := EndpointTailRootSeries.ratio_inverse (ξ*exp (-z)) (mul_ne_zero hξ (exp_ne_zero _))
  have hi : (ξ*exp (-z))⁻¹ = ξ⁻¹*exp z := by
    rw [mul_inv_rev, ← Complex.exp_neg, neg_neg, mul_comm]
  rw [hi] at he
  exact he.symm

theorem rootTerm_pole (n l : ℕ) (ξ w : ℂ) (hξ : ξ^5=1) :
    rootTerm n ξ w l = x n w^(l+1)/((l+1:ℕ):ℂ)*
      (pole (ξ^(l+1)) (((l+1:ℕ):ℂ)*w)-1/(exp (5*(((l+1:ℕ):ℂ)*w))-1)) := by
  have hξ0 : ξ ≠ 0 := by intro he; simp [he] at hξ
  unfold rootTerm x
  rw [zpow_neg, zpow_natCast, inverse_pole _ _ (pow_ne_zero _ hξ0)]
  rw [mul_assoc (5:ℂ)]

theorem errorTerm_bound (n l : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    ‖errorTerm n ξ w l‖ ≤ 5*‖w‖*‖x n w‖^(l+1) := by
  have hk : (0:ℝ) < ((l+1:ℕ):ℝ) := by positivity
  have hs := WedgePoleDifference.scale_wedge w hw.le hi ((l+1:ℕ):ℝ) hk.le
  have hp : 0 < (((l+1:ℕ):ℂ)*w).re := by simpa using mul_pos hk hw
  have hb := kernel_remainder_bound (ξ^(l+1)) (((l+1:ℕ):ℂ)*w) (power_fifth ξ hξ _) hp (by exact_mod_cast hs.2)
  have he : errorTerm n ξ w l = x n w^(l+1)/((l+1:ℕ):ℂ)*
      ((pole (ξ^(l+1)) (((l+1:ℕ):ℂ)*w)-1/(exp (5*(((l+1:ℕ):ℂ)*w))-1))-
        principal (ξ^(l+1)) (((l+1:ℕ):ℂ)*w)) := by
    unfold errorTerm mainTerm
    rw [rootTerm_pole n l ξ w hξ]
    ring
  rw [he, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (‖x n w‖^(l+1)/((l+1:ℕ):ℝ))*(5*‖((l+1:ℕ):ℂ)*w‖) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      rw [norm_mul, Complex.norm_natCast]
      field_simp

theorem x_norm_lt_one (n : ℕ) (w : ℂ) (hn : 0 < n) (hw : 0 < w.re) : ‖x n w‖ < 1 := by
  rw [x, Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero, zero_mul, sub_zero]
  have hp : (0:ℝ) < ((5*n:ℕ):ℝ) := by positivity
  nlinarith

theorem error_majorant_hasSum (n : ℕ) (w : ℂ) (hn : 0 < n) (hw : 0 < w.re) :
    HasSum (fun l : ℕ => 5*‖w‖*‖x n w‖^(l+1)) (5*‖w‖*‖x n w‖/(1-‖x n w‖)) := by
  have hg := (hasSum_geometric_of_lt_one (norm_nonneg (x n w)) (x_norm_lt_one n w hn hw)).mul_left
    (5*‖w‖*‖x n w‖)
  have he : (5*‖w‖*‖x n w‖)*(1-‖x n w‖)⁻¹ = 5*‖w‖*‖x n w‖/(1-‖x n w‖) := by ring
  rw [he] at hg
  exact hg.congr_fun (fun l => by rw [pow_succ]; ring)

theorem errorTerm_summable (n : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) : Summable (errorTerm n ξ w) := by
  apply (error_majorant_hasSum n w hn hw).summable.of_norm_bounded
  exact fun l => errorTerm_bound n l ξ w hξ hw hi

theorem sharp_error_bound (n : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    ‖∑' l : ℕ, errorTerm n ξ w l‖ ≤ 5*‖w‖*‖x n w‖/(1-‖x n w‖) := by
  have hs := errorTerm_summable n ξ w hξ hn hw hi
  have hm := error_majorant_hasSum n w hn hw
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    ((hs.norm.tsum_le_tsum (fun l => errorTerm_bound n l ξ w hξ hw hi) hm.summable).trans_eq hm.tsum_eq)

theorem root_norm (ξ w : ℂ) (hξ : ξ^5=1) (hw : 0 < w.re) : ‖ξ*exp (-w)‖ < 1 := by
  rw [norm_mul, FiveRootProductExpansion.root_norm ξ hξ, one_mul, Complex.norm_exp, Complex.neg_re]
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem mainTerm_summable (n : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) : Summable (mainTerm n ξ w) := by
  have hs := (rootTerm_summable n ξ w hξ (root_norm ξ w hξ hw)).sub
    (errorTerm_summable n ξ w hξ hn hw hi)
  exact hs.congr (fun l => by simp only [errorTerm]; ring)

theorem tailLog_decomposition (n : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    EndpointTailLog.tailLog n (ξ*exp (-w)) =
      (∑' l : ℕ, mainTerm n ξ w l)+(∑' l : ℕ, errorTerm n ξ w l) := by
  rw [← (mainTerm_summable n ξ w hξ hn hw hi).tsum_add
    (errorTerm_summable n ξ w hξ hn hw hi), tailLog_root_series n ξ w hξ (root_norm ξ w hξ hw)]
  apply tsum_congr
  intro l
  simp only [errorTerm]
  ring

end
end Borwein.EndpointSharpTail
