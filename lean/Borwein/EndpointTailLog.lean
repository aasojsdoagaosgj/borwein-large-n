import Borwein.EndpointFiniteConnection

set_option autoImplicit false

namespace Borwein.EndpointTailLog
noncomputable section
open Complex EndpointEta EndpointEulerTail EndpointFiniteConnection

/-- A logarithm defined by the convergent sum of individual factor logs.
It is not asserted to be the principal logarithm of the entire product. -/
def inverseLog (N : ℕ) (q : ℂ) : ℂ := -∑' j : ℕ, log (1-q^(j+N+1))
def tailLog (n : ℕ) (q : ℂ) : ℂ := inverseLog (5*n) q-inverseLog n (q^5)

theorem log_summable (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun j : ℕ => log (1-q^(j+N+1))) := by
  have h := Complex.summable_log_one_add_of_summable (tail_summable N q hq).of_norm
  simpa only [← sub_eq_add_neg] using h

theorem exp_inverseLog (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    exp (inverseLog N q) = (tailEuler N q)⁻¹ := by
  rw [inverseLog, Complex.exp_neg]
  rw [Complex.cexp_tsum_eq_tprod (fun j => factor_ne_zero q hq (j+N+1) (by omega))
    (log_summable N q hq)]
  rfl

theorem exp_tailLog (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    exp (tailLog n q) = tail n q := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  rw [tailLog, Complex.exp_sub, exp_inverseLog _ q hq, exp_inverseLog _ (q^5) hq5]
  simp only [tail, div_eq_mul_inv, inv_inv]
  ring

theorem polynomial_eq_G_exp (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Polynomial.eval₂ (Int.castRingHom ℂ) q (Borwein.polynomial n) = G q*exp (tailLog n q) := by
  rw [exp_tailLog n q hq]
  exact polynomial_eq_G_tail n q hq

theorem log_factor_bound (N j : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖log (1-q^(j+N+1))‖ ≤ ‖q‖^(j+N+1)/(1-‖q‖) := by
  have hp : ‖q‖^(j+N+1) ≤ ‖q‖ := by
    rw [pow_succ]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq.le)
  have hn : ‖-q^(j+N+1)‖ < 1 := by simp only [norm_neg, norm_pow]; exact hp.trans_lt hq
  have he := Complex.norm_log_sub_logTaylor_le 0 hn
  have he' : ‖log (1-q^(j+N+1))‖ ≤ ‖q‖^(j+N+1)/(1-‖q‖^(j+N+1)) := by
    simpa [Complex.logTaylor, div_eq_mul_inv, ← sub_eq_add_neg] using he
  apply he'.trans
  exact div_le_div₀ (by positivity) le_rfl (by linarith) (by linarith)

theorem inverseLog_bound (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖inverseLog N q‖ ≤ ‖q‖^(N+1)/(1-‖q‖)^2 := by
  have hs : HasSum (fun j : ℕ => ‖q‖^(j+N+1)) (‖q‖^(N+1)/(1-‖q‖)) := by
    simpa [pow_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_lt_one (norm_nonneg q) hq).mul_left (‖q‖^(N+1))
  have hb := hs.div_const (1-‖q‖)
  rw [inverseLog, norm_neg]
  calc
    _ ≤ ∑' j : ℕ, ‖log (1-q^(j+N+1))‖ := norm_tsum_le_tsum_norm (log_summable N q hq).norm
    _ ≤ ∑' j : ℕ, ‖q‖^(j+N+1)/(1-‖q‖) :=
      (log_summable N q hq).norm.tsum_le_tsum (fun j => log_factor_bound N j q hq) hb.summable
    _ = _ := by rw [hb.tsum_eq, div_div, ← pow_two]

/-- Eta error for the finite polynomial after retaining the exact tail exponential. -/
theorem polynomial_normalized_root (n : ℕ) (j : Fin 4) (v y : ℝ) (hv : 0 < v)
    (hV : v ≤ 13/10000) (hy : |y| ≤ 3*v/4) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ)
        (FivePoleCircle.zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I))) (Borwein.polynomial n)/
      (EndpointRootAsymptotic.kappa j*EndpointRootAsymptotic.main ((v:ℂ)+(y:ℂ)*I)*
        exp (tailLog n (FivePoleCircle.zeta^(j.val+1)*exp (-((v:ℂ)+(y:ℂ)*I)))))-1‖ ≤
          10*Real.exp (-1/v) := by
  let w : ℂ := (v:ℂ)+(y:ℂ)*I
  let z : ℂ := FivePoleCircle.zeta^(j.val+1)*exp (-w)
  have hw : 0 < w.re := by simpa [w] using hv
  have hz : ‖z‖ < 1 := root_norm j w hw
  have hkm : EndpointRootAsymptotic.kappa j*EndpointRootAsymptotic.main w ≠ 0 :=
    mul_ne_zero (EndpointRootAsymptotic.kappa_ne_zero j) (Complex.exp_ne_zero _)
  change ‖Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n)/
    (EndpointRootAsymptotic.kappa j*EndpointRootAsymptotic.main w*exp (tailLog n z))-1‖ ≤ _
  rw [polynomial_eq_G_exp n z hz]
  have hG := EndpointRootAsymptotic.four_root_expansion j w hw
  change G z = _ at hG
  rw [hG]
  have he : (EndpointRootAsymptotic.kappa j*EndpointRootAsymptotic.main w*
      EndpointRootAsymptotic.correction j w*exp (tailLog n z))/
      (EndpointRootAsymptotic.kappa j*EndpointRootAsymptotic.main w*exp (tailLog n z)) =
        EndpointRootAsymptotic.correction j w := by
    rw [mul_div_mul_right _ _ (Complex.exp_ne_zero _), mul_div_cancel_left₀ _ hkm]
  rw [he]
  exact EndpointRootAsymptotic.correction_error j v y hv hV hy

end
end Borwein.EndpointTailLog
