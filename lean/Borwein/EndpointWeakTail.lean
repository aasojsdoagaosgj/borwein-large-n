import Borwein.EndpointCombinedTail

set_option autoImplicit false

namespace Borwein.EndpointWeakTail
noncomputable section
open Complex FivePoleCircle EndpointRootCancellation EndpointTailMain EndpointSharpTail
open EndpointFiniteTailExpansion EndpointCombinedTail

def filtered (a n : ℕ) (w : ℂ) : ℂ := ∑ j : Fin 4, weight a j*
  (EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-w))-1)
def filteredMain (a n : ℕ) (w : ℂ) : ℂ := EndpointRootAsymptotic.main w*filtered a n w
def weakLeading (n : ℕ) (w : ℂ) : ℂ := -x n w*exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)

theorem filtered_eq (a n : ℕ) (ha : a=3 ∨ a=4) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    filtered a n w=exp (lambda (x n w)/(5*w))*perturbed a n w := by
  have he : filtered a n w=exp (lambda (x n w)/(5*w))*perturbed a n w-constant a := by
    unfold filtered perturbed constant
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← EndpointTailLog.exp_tailLog n _ (EndpointFiniteConnection.root_norm j w hw),
      tailLog_eq n _ w (actual_root_primitive j) hn hw hi]
    simp only [exp_add]
    ring
  simpa only [weak_constant a ha, sub_zero] using he

theorem filteredMain_eq (a n : ℕ) (ha : a=3 ∨ a=4) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    filteredMain a n w=exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)*perturbed a n w := by
  rw [filteredMain, filtered_eq a n ha w hn hw hi, EndpointRootAsymptotic.main, ← mul_assoc, ← exp_add]
  congr 2
  rw [← radial_exponent n w hn hw]
  ring

theorem weakLeading_ne_zero (n : ℕ) (w : ℂ) : weakLeading n w ≠ 0 :=
  mul_ne_zero (neg_ne_zero.mpr (exp_ne_zero _)) (exp_ne_zero _)

theorem normalized_identity (a n : ℕ) (ha : a=3 ∨ a=4) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    filteredMain a n w/weakLeading n w-1 = -(perturbed a n w+x n w)/x n w := by
  rw [filteredMain_eq a n ha w hn hw hi, weakLeading]
  have hx : x n w ≠ 0 := exp_ne_zero _
  have he := exp_ne_zero ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)
  field_simp
  ring

theorem normalized_error (a n : ℕ) (ha : a=3 ∨ a=4) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4)
    (hr : ‖x n w‖ ≤ 1/100) (hwn : ‖w‖ ≤ 1/100) :
    ‖filteredMain a n w/weakLeading n w-1‖ ≤ 8*‖x n w‖+25*‖w‖ := by
  rw [normalized_identity a n ha w hn hw hi, norm_div, norm_neg]
  have hx : 0 < ‖x n w‖ := norm_pos_iff.mpr (exp_ne_zero _)
  exact (div_le_iff₀ hx).mpr (weak_perturbed_remainder a n ha w hn hw hi hr hwn)

theorem box_norm (v y : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) :
    ‖(v:ℂ)+(y:ℂ)*I‖ ≤ 1/100 := by
  have h := norm_add_le (v:ℂ) ((y:ℂ)*I)
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_of_pos hv] at h
  linarith

theorem exponential_threshold : (100:ℝ) ≤ Real.exp (11/2) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 11/2) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem box_x_norm (n : ℕ) (v y : ℝ) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖x n ((v:ℂ)+(y:ℂ)*I)‖ ≤ 1/100 := by
  rw [EndpointFiniteTailExpansion.x_norm]
  have he := exponential_threshold.trans (Real.exp_le_exp.mpr hτ)
  have hi := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<100) he
  simpa [neg_mul, Real.exp_neg, one_div] using hi

/-- The weak-mode main expression in manuscript (5.9), including its relative error bound. -/
theorem weak_endpoint_expansion (a n : ℕ) (ha : a=3 ∨ a=4) (v y : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ∃ ε : ℂ, ‖ε‖ ≤ 8*Real.exp (-((5*n:ℕ):ℝ)*v)+25*‖(v:ℂ)+(y:ℂ)*I‖ ∧
      filteredMain a n ((v:ℂ)+(y:ℂ)*I) = weakLeading n ((v:ℂ)+(y:ℂ)*I)*(1+ε) := by
  let w : ℂ := (v:ℂ)+(y:ℂ)*I
  have hw : 0 < w.re := by simpa [w] using hv
  have hi : |w.im| ≤ 3*w.re/4 := by simpa [w] using hy
  refine ⟨filteredMain a n w/weakLeading n w-1, ?_, ?_⟩
  · have h := normalized_error a n ha w hn hw hi (box_x_norm n v y hτ) (box_norm v y hv hV hy)
    simpa [EndpointFiniteTailExpansion.x_norm, w] using h
  · have he := weakLeading_ne_zero n w
    change filteredMain a n w = weakLeading n w*(1+(filteredMain a n w/weakLeading n w-1))
    field_simp
    ring

end
end Borwein.EndpointWeakTail
