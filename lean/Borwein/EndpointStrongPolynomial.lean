import Borwein.EndpointStrongPhase
import Borwein.EndpointEtaTailBound

set_option autoImplicit false

namespace Borwein.EndpointStrongPolynomial
noncomputable section
open Complex FivePoleCircle EndpointRootAsymptotic EndpointRootCancellation EndpointTailMain
open EndpointSharpTail EndpointFiniteTailExpansion EndpointCombinedTail EndpointStrongConstants
open EndpointWeakPolynomial EndpointTailGlobalLog

def polynomialSum (a n : ℕ) (w : ℂ) : ℂ := ∑ j : Fin 4, character a j*
  Polynomial.eval₂ (Int.castRingHom ℂ) (zeta^(j.val+1)*exp (-w)) (Borwein.polynomial n)
def mainTail (a n : ℕ) (w : ℂ) : ℂ := main w*∑ j : Fin 4, weight a j*
  EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-w))
def strongEta (a n : ℕ) (w : ℂ) : ℂ := ∑ j : Fin 4, character a j*
  (EndpointEta.G (zeta^(j.val+1)*exp (-w))-kappa j*main w)*
    EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-w))
def leading (a : Fin 3) (n : ℕ) (w : ℂ) : ℂ := constant a.val*
  exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)

theorem mainTail_eq (a n : ℕ) (w : ℂ) (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    mainTail a n w=exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)*perturbed a n w := by
  have hc : main w*exp (lambda (x n w)/(5*w)) =
      exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6) := by
    rw [main, ← exp_add, ← radial_exponent n w hn hw]
    congr 1
    ring
  rw [mainTail, ← hc, perturbed, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← EndpointTailLog.exp_tailLog n _ (EndpointFiniteConnection.root_norm j w hw),
    tailLog_eq n _ w (actual_root_primitive j) hn hw hi]
  simp only [exp_add]
  ring

theorem polynomial_decomposition (a n : ℕ) (w : ℂ) (hw : 0 < w.re) :
    polynomialSum a n w=mainTail a n w+strongEta a n w := by
  unfold polynomialSum mainTail strongEta
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [EndpointFiniteConnection.polynomial_eq_G_tail n _ (EndpointFiniteConnection.root_norm j w hw)]
  unfold character weight
  ring

theorem strongEta_factored (a n : ℕ) (w : ℂ) (hw : 0 < w.re) :
    strongEta a n w = ∑ j : Fin 4, weight a j*main w*(correction j w-1)*
      EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-w)) := by
  unfold strongEta
  apply Finset.sum_congr rfl
  intro j _
  rw [EndpointRootAsymptotic.four_root_expansion j w hw]
  unfold character weight
  ring

theorem strong_eta_bound (a n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ‖strongEta a n ((v:ℂ)+(y:ℂ)*I)‖ ≤ 40*‖main ((v:ℂ)+(y:ℂ)*I)‖*Real.exp (-1/v)*
      (1+(radialX n v/v)*Real.exp (radialX n v/v)) := by
  rw [strongEta_factored a n _ (by simpa using hv)]
  apply (norm_sum_le _ _).trans
  have hB : 0 ≤ 1+(radialX n v/v)*Real.exp (radialX n v/v) := by unfold radialX; positivity
  have hb : ∑ j : Fin 4, ‖weight a j*main ((v:ℂ)+(y:ℂ)*I)*(correction j ((v:ℂ)+(y:ℂ)*I)-1)*
      EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))‖ ≤
      ∑ _j : Fin 4, ‖main ((v:ℂ)+(y:ℂ)*I)‖*(10*Real.exp (-1/v))*
        (1+(radialX n v/v)*Real.exp (radialX n v/v)) := by
    apply Finset.sum_le_sum
    intro j _
    have hT := EndpointEtaTailBound.root_tail_bound n j v y hn hv hV hτ
    have ht := norm_add_le (EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))-1) (1:ℂ)
    simp only [sub_add_cancel, norm_one] at ht
    have htn : ‖EndpointFiniteConnection.tail n (zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))‖ ≤
        1+(radialX n v/v)*Real.exp (radialX n v/v) := by linarith
    simp only [norm_mul, EndpointRootLinear.weight_norm, one_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (correction_error j v y hv hV hy) (norm_nonneg _))
      htn (norm_nonneg _) (by positivity)
  exact hb.trans_eq (by simp; ring)

theorem leading_ne_zero (a : Fin 3) (n : ℕ) (w : ℂ) : leading a n w ≠ 0 :=
  mul_ne_zero (constant_ne_zero a) (exp_ne_zero _)

theorem main_relative_error (a : Fin 3) (n : ℕ) (w : ℂ) (hn : 0 < n)
    (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4)
    (hr : ‖x n w‖ ≤ 1/100) (hwn : ‖w‖ ≤ 1/100) :
    ‖mainTail a.val n w/leading a n w-1‖ ≤ 8*‖x n w‖+25*‖w‖ := by
  rw [mainTail_eq a.val n w hn hw hi, leading]
  have hc := constant_ne_zero a
  have hex := exp_ne_zero ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)
  have he : exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)*perturbed a.val n w/
      (constant a.val*exp ((n:ℂ)*PhaseIntegral.complexR (((5*n:ℕ):ℂ)*w)-w/6)) = perturbed a.val n w/constant a.val := by field_simp
  rw [he]
  exact EndpointStrongPhase.perturbed_relative_error a n w hn hw hi hr hwn

theorem strong_endpoint_expansion (a : Fin 3) (n : ℕ) (v y : ℝ)
    (hn : 0 < n) (hv : 0 < v) (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4)
    (hτ : 11/2 ≤ ((5*n:ℕ):ℝ)*v) :
    ∃ ε : ℂ, ‖ε‖ ≤ 8*Real.exp (-((5*n:ℕ):ℝ)*v)+25*‖(v:ℂ)+(y:ℂ)*I‖ ∧
      mainTail a.val n ((v:ℂ)+(y:ℂ)*I) = leading a n ((v:ℂ)+(y:ℂ)*I)*(1+ε) := by
  let w : ℂ := (v:ℂ)+(y:ℂ)*I
  have hw : 0 < w.re := by simpa [w] using hv
  have hi : |w.im| ≤ 3*w.re/4 := by simpa [w] using hy
  refine ⟨mainTail a.val n w/leading a n w-1, ?_, ?_⟩
  · have h := main_relative_error a n w hn hw hi (EndpointWeakTail.box_x_norm n v y hτ) (EndpointWeakTail.box_norm v y hv hV hy)
    simpa [EndpointFiniteTailExpansion.x_norm, w] using h
  · have he := leading_ne_zero a n w
    change mainTail a.val n w = leading a n w*(1+(mainTail a.val n w/leading a n w-1))
    field_simp
    ring

end
end Borwein.EndpointStrongPolynomial
