import Borwein.LogFactorDerivatives

namespace Borwein.LogFactorDerivatives
noncomputable section
open scoped BigOperators
open MeasureTheory Set

theorem third_norm_bound (c z : ℂ) (x d : ℝ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re)
    (hx : 0 ≤ x) (hd : 0 < d) (hgap : d ≤ ‖kernel c z x‖) :
    ‖f3 c z x‖ ≤ 2*‖z‖^3/d^3 := by
  have hw := w_norm_le_one c z x hc hz hx
  have hsum : ‖1+w c z x‖ ≤ 2 := by
    have h := norm_add_le (1:ℂ) (w c z x)
    norm_num at h
    linarith
  calc
    _ = ‖z‖^3*‖w c z x‖*‖1+w c z x‖/‖kernel c z x‖^3 := by simp [f3,norm_div,norm_mul,norm_pow]
    _ ≤ ‖z‖^3*1*2/d^3 := by gcongr
    _ = _ := by ring

theorem uniform_kernel_ne_zero (c z : ℂ) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖) :
    ∀ x ∈ Icc (0:ℝ) 1, kernel c z x ≠ 0 := by
  intro x hx
  exact norm_pos_iff.mp (hd.trans_le (hgap x hx))

theorem uniform_slit (c z : ℂ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖) :
    ∀ x ∈ Icc (0:ℝ) 1, kernel c z x ∈ Complex.slitPlane := by
  intro x hx
  exact slit_of_norm_le_one (w c z x) (w_norm_le_one c z x hc hz hx.1)
    (uniform_kernel_ne_zero c z d hd hgap x hx)

theorem third_integral_bound (c z : ℂ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖) :
    (∫ x in (0:ℝ)..1, ‖f3 c z x‖) ≤ 2*‖z‖^3/d^3 := by
  have hi : IntervalIntegrable (fun x => ‖f3 c z x‖) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa using (third_continuousOn c z _ (uniform_kernel_ne_zero c z d hd hgap)).norm
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hi
    (intervalIntegrable_const (c := 2*‖z‖^3/d^3))
    (fun x hx => third_norm_bound c z x d hc hz hx.1 hd (hgap x hx))
  simpa using h

theorem log_error_bound (c z : ℂ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) :
    ‖(∑ k ∈ Finset.range n, f0 c z (((k:ℝ)+α)/n))-(n:ℝ) • (∫ x in (0:ℝ)..1, f0 c z x)-
      PeanoQuadrature.B1 α • (f0 c z 1-f0 c z 0)-
      (PeanoQuadrature.B2 α/(2*n)) • (f1 c z 1-f1 c z 0)‖ ≤
      (n:ℝ)⁻¹^2 * (2*‖z‖^3/d^3) := by
  have hk := uniform_kernel_ne_zero c z d hd hgap
  have hs := uniform_slit c z hc hz d hd hgap
  have h := EulerMaclaurin.error_bound n hn α ha0 ha1 (f0 c z) (f1 c z) (f2 c z) (f3 c z)
    (fun x hx => log_deriv c z x (hs x hx))
    (fun x hx => first_deriv c z x (hk x hx))
    (fun x hx => second_deriv c z x (hk x hx))
    (third_continuousOn c z _ hk)
  exact h.trans (mul_le_mul_of_nonneg_left (third_integral_bound c z hc hz d hd hgap) (sq_nonneg _))

end
end Borwein.LogFactorDerivatives
