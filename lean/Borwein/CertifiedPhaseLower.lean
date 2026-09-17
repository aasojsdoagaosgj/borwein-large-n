import Borwein.ElementaryPhaseLower
import Borwein.CertifiedMomentTable

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Borwein.CertifiedPhaseLower
noncomputable section
open CertifiedMomentTable MomentExponentData ExplicitPhaseProfile CombinedPhaseSign

def qLo (i : Fin 32) : ℝ := (lo[64*(i.val+1)]!:ℝ)/D
def qHi (i : Fin 32) : ℝ := (hi[64*i.val]!:ℝ)/D
def bound (a : ℕ) (i : Fin 32) : ℝ :=
  if a = 0 then 3 else if a = 1 then 9/10 else if a = 2 then 7/10 else
    if a = 3 then (7/10)*(qLo i/(1+qHi i)) else (17/20)*(qLo i/(1+qHi i))

theorem q_bounds (i : Fin 32) (τ : ℝ) (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) :
    qLo i ≤ Real.exp (-τ) ∧ Real.exp (-τ) ≤ qHi i := by
  have hlo := (CertifiedMomentExponent.all_bounds (64*(i.val+1)) (by omega)).1
  have hhi := (CertifiedMomentExponent.all_bounds (64*i.val) (by omega)).2
  have heL : -(11/4096:ℝ)*((64*(i.val+1):ℕ):ℝ) = -tauHi i := by
    dsimp [tauHi]
    push_cast
    ring
  have heU : -(11/4096:ℝ)*((64*i.val:ℕ):ℝ) = -tauLo i := by
    dsimp [tauLo]
    push_cast
    ring
  rw [heL] at hlo
  rw [heU] at hhi
  exact ⟨hlo.trans (Real.exp_le_exp.mpr (by linarith)),
    (Real.exp_le_exp.mpr (by linarith : -τ ≤ -tauLo i)).trans hhi⟩

theorem lower_nat_pos (i : Fin 32) : 0 < lo[64*(i.val+1)]! := by
  revert i
  decide +kernel

theorem qLo_pos (i : Fin 32) : 0 < qLo i := by
  exact div_pos (by exact_mod_cast lower_nat_pos i) (by norm_num [D])

theorem qHi_nonneg (i : Fin 32) : 0 ≤ qHi i := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem bound_pos (a : ℕ) (i : Fin 32) : 0 < bound a i := by
  have hl := qLo_pos i
  have hu := qHi_nonneg i
  unfold bound
  split_ifs <;> positivity

theorem bound_le_lower (a : ℕ) (i : Fin 32) (τ : ℝ) (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) :
    bound a i ≤ ElementaryPhaseLower.lower a τ := by
  have h := q_bounds i τ hL hU
  have hd : qLo i/(1+qHi i) ≤ Real.exp (-τ)/(1+Real.exp (-τ)) :=
    div_le_div₀ (Real.exp_pos _).le h.1 (by positivity) (by linarith [h.2])
  unfold bound ElementaryPhaseLower.lower
  split_ifs
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left hd (by norm_num)
  · exact mul_le_mul_of_nonneg_left hd (by norm_num)

theorem signed_phase (a : ℕ) (ha : a < 5) (i : Fin 32) (τ : ℝ)
    (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) : bound a i ≤ sign a*phase a τ := by
  have hτ : 0 ≤ τ := (show 0 ≤ tauLo i by unfold tauLo; positivity).trans hL
  exact (bound_le_lower a i τ hL hU).trans (ElementaryPhaseLower.signed_phase_lower a ha τ hτ)

theorem signed_psi_real (a : ℕ) (ha : a < 5) (i : Fin 32) (τ : ℝ)
    (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) :
    bound a i ≤ sign a*(CombinedAmplitude.psi FivePoleCircle.zeta a (τ:ℂ)).re := by
  have hτ : 0 ≤ τ := (show 0 ≤ tauLo i by unfold tauLo; positivity).trans hL
  rw [psi_eq_profile a ha τ hτ,Complex.ofReal_re]
  exact signed_phase a ha i τ hL hU

theorem all_tau_bounds (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    ∃ i : Fin 32, tauLo i ≤ τ ∧ τ ≤ tauHi i ∧
      ∀ a < 5, 0 < bound a i ∧ bound a i ≤ sign a*phase a τ := by
  obtain ⟨i,hi⟩ := cell_cover τ hτ hT
  exact ⟨i,hi.1,hi.2,fun a ha => ⟨bound_pos a i,signed_phase a ha i τ hi.1 hi.2⟩⟩

end
end Borwein.CertifiedPhaseLower
