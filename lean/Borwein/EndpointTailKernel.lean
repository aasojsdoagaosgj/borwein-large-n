import Borwein.WedgeExponentialKernel
import Borwein.WedgePoleDifference
import Borwein.EndpointTailRootSeries

set_option autoImplicit false

namespace Borwein.EndpointTailKernel
noncomputable section
open Complex WedgeRootKernel

def regular (z : ℂ) : ℂ := 1/(exp z-1)-1/z+1/2

theorem regular_bound (z : ℂ) (hz : 0 < z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖regular z‖ ≤ ‖z‖/12 := by
  apply WedgeExponentialKernel.shifted_bound z hz
  have hs := (sq_le_sq₀ (abs_nonneg z.im) (by positivity : 0 ≤ 3*z.re/4)).mpr hi
  rw [sq_abs] at hs
  simp only [pow_two, Complex.mul_re]
  nlinarith

theorem regular_scaled_bound (z : ℂ) (hz : 0 < z.re) (hi : |z.im| ≤ 3*z.re/4)
    (c : ℝ) (hc : 0 < c) : ‖regular ((c:ℂ)*z)‖ ≤ c*‖z‖/12 := by
  have hs := WedgePoleDifference.scale_wedge z hz.le hi c hc.le
  have hp : 0 < ((c:ℂ)*z).re := by simpa using mul_pos hc hz
  have hb := regular_bound ((c:ℂ)*z) hp hs.2
  simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le] using hb

theorem pole_one (z : ℂ) : pole 1 z = 1/(exp z-1) := by
  have he := EndpointTailRootSeries.ratio_inverse (exp (-z)) (exp_ne_zero _)
  simpa only [pole, one_mul, ← Complex.exp_neg, neg_neg] using he

theorem nonresonant_bound (ξ z : ℂ) (hξ : ξ^5=1) (hne : ξ ≠ 1)
    (hz : 0 < z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖(pole ξ z-1/(exp (5*z)-1))-(-1/(5*z)+ξ/(1-ξ)+1/2)‖ ≤ 5*‖z‖ := by
  have h1 := WedgePoleDifference.difference_at_zero ξ z hξ hne hz.le hi
  have h2 := regular_scaled_bound z hz hi 5 (by norm_num)
  norm_num only [Complex.ofReal_ofNat] at h2
  have he : (pole ξ z-1/(exp (5*z)-1))-(-1/(5*z)+ξ/(1-ξ)+1/2) =
      (pole ξ z-ξ/(1-ξ))-regular (5*z) := by unfold regular; ring
  rw [he]
  have hb := norm_sub_le (pole ξ z-ξ/(1-ξ)) (regular (5*z))
  linarith [norm_nonneg z]

theorem resonant_bound (z : ℂ) (hz : 0 < z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖(pole 1 z-1/(exp (5*z)-1))-4/(5*z)‖ ≤ ‖z‖/2 := by
  have h1 := regular_bound z hz hi
  have h2 := regular_scaled_bound z hz hi 5 (by norm_num)
  norm_num only [Complex.ofReal_ofNat] at h2
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have he : (pole 1 z-1/(exp (5*z)-1))-4/(5*z) = regular z-regular (5*z) := by
    rw [pole_one]
    unfold regular
    field_simp
    ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

def principal (ξ z : ℂ) : ℂ :=
  if ξ=1 then 4/(5*z) else -1/(5*z)+ξ/(1-ξ)+1/2

theorem kernel_remainder_bound (ξ z : ℂ) (hξ : ξ^5=1)
    (hz : 0 < z.re) (hi : |z.im| ≤ 3*z.re/4) :
    ‖(pole ξ z-1/(exp (5*z)-1))-principal ξ z‖ ≤ 5*‖z‖ := by
  by_cases he : ξ=1
  · subst ξ
    simp only [principal, if_pos rfl]
    exact (resonant_bound z hz hi).trans (by linarith [norm_nonneg z])
  · simpa only [principal, if_neg he] using nonresonant_bound ξ z hξ he hz hi

end
end Borwein.EndpointTailKernel
