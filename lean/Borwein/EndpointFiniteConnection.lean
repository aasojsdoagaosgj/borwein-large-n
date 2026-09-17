import Borwein.EndpointEulerTail
import Borwein.EndpointRootAsymptotic
import Borwein.ProductSmoothing

set_option autoImplicit false

namespace Borwein.EndpointFiniteConnection
noncomputable section
open Complex EndpointEta EndpointEulerTail

def tail (n : ℕ) (q : ℂ) : ℂ := tailEuler n (q^5)/tailEuler (5*n) q

theorem polynomial_step (n : ℕ) (q : ℂ) :
    Polynomial.eval₂ (Int.castRingHom ℂ) q (Borwein.polynomial (n+1)) =
      Polynomial.eval₂ (Int.castRingHom ℂ) q (Borwein.polynomial n)*
        ∏ a : Fin 4, (1-q^Borwein.exponent n a) := by
  simp [Borwein.polynomial, Borwein.block, Finset.prod_range_succ, Polynomial.eval₂_finsetProd]

theorem finiteEuler_step_five (n : ℕ) (q : ℂ) :
    finiteEuler (5*(n+1)) q = finiteEuler (5*n) q*
      (∏ a : Fin 4, (1-q^Borwein.exponent n a))*(1-(q^5)^(n+1)) := by
  rw [show 5*(n+1) = 5*n+5 by omega]
  unfold finiteEuler
  rw [Finset.prod_range_add]
  norm_num [Finset.prod_range_succ, Fin.prod_univ_four, Borwein.exponent, ← pow_mul]
  have he : 5*(n+1)=5*n+5 := by omega
  rw [he]
  ring

theorem finiteEuler_polynomial (n : ℕ) (q : ℂ) :
    finiteEuler (5*n) q = Polynomial.eval₂ (Int.castRingHom ℂ) q (Borwein.polynomial n)*
      finiteEuler n (q^5) := by
  induction n with
  | zero => simp [finiteEuler, Borwein.polynomial]
  | succ n ih =>
    rw [finiteEuler_step_five, ih, polynomial_step]
    have he : finiteEuler (n+1) (q^5) = finiteEuler n (q^5)*(1-(q^5)^(n+1)) := by
      simp [finiteEuler, Finset.prod_range_succ]
    rw [he]
    ring

/-- Exact analytic identity B_n = G T_n on the open unit disk. -/
theorem polynomial_eq_G_tail (n : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Polynomial.eval₂ (Int.castRingHom ℂ) q (Borwein.polynomial n) = G q*tail n q := by
  have hq5 : ‖q^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  have hF := finiteEuler_ne_zero n (q^5) hq5
  have hT := tailEuler_ne_zero (5*n) q hq
  have hT5 := tailEuler_ne_zero n (q^5) hq5
  unfold G tail
  rw [← euler_split (5*n) q hq, ← euler_split n (q^5) hq5, finiteEuler_polynomial]
  field_simp

theorem root_norm (j : Fin 4) (w : ℂ) (hw : 0 < w.re) :
    ‖FivePoleCircle.zeta^(j.val+1)*exp (-w)‖ < 1 := by
  rw [← EndpointRootAsymptotic.root_coordinate]
  apply EndpointCuspConjugation.q_norm_lt_one
  have hs := EndpointRootAsymptotic.sPoint_upper w hw
  simpa using div_pos hs (by norm_num : (0:ℝ)<5)

/-- The exact eta expansion is now attached to the original finite polynomial. -/
theorem polynomial_root_expansion (n : ℕ) (j : Fin 4) (w : ℂ) (hw : 0 < w.re) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (FivePoleCircle.zeta^(j.val+1)*exp (-w))
        (Borwein.polynomial n) =
      EndpointRootAsymptotic.kappa j*EndpointRootAsymptotic.main w*
        EndpointRootAsymptotic.correction j w*
        tail n (FivePoleCircle.zeta^(j.val+1)*exp (-w)) := by
  rw [polynomial_eq_G_tail n _ (root_norm j w hw), EndpointRootAsymptotic.four_root_expansion j w hw]

end
end Borwein.EndpointFiniteConnection
