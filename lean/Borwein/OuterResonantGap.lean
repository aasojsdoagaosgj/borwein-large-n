import Borwein.OuterArcGeometry
import Borwein.CertifiedResonantGap

namespace Borwein.OuterResonantGap
noncomputable section
open OuterArcGeometry DirichletCover

theorem denominator_five_modulus (n Q : ℕ) (τ θ : ℝ) (hn : 0 < n) (hQ : 2 ≤ Q)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (hθ : region n (6/5) θ) (q : ℚ)
    (hq : Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5) :
    SmoothedPhase.smoothedModulus (113/40000) τ (localAngle n θ q) <
      PhaseIntegral.radialR τ-(31:ℝ)/3125 := by
  apply CertifiedResonantGap.smoothed_modulus_gap _ _ hτ0 hτ1
  exact denominator_five_local_lower n Q (6/5) θ hn hQ (by norm_num) hθ q hq hb

theorem denominator_five_exponential (n Q : ℕ) (τ θ : ℝ) (hn : 0 < n) (hQ : 2 ≤ Q)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (hθ : region n (6/5) θ) (q : ℚ)
    (hq : Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5) :
    Real.exp ((n:ℝ)*SmoothedPhase.smoothedModulus (113/40000) τ (localAngle n θ q)) <
      Real.exp ((n:ℝ)*PhaseIntegral.radialR τ)*Real.exp (-(31:ℝ)/3125*n) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hg := mul_lt_mul_of_pos_left (denominator_five_modulus n Q τ θ hn hQ hτ0 hτ1 hθ q hq hb) hn0
  rw [← Real.exp_add]
  apply Real.exp_lt_exp.mpr
  nlinarith

theorem exists_outer_cusp (n Q : ℕ) (τ θ : ℝ) (hn : 0 < n) (hQ : 2 ≤ Q)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) (hθ : region n (6/5) θ) :
    ∃ q ∈ CompactCuspCover.candidates Q,
      Near (θ/(2*Real.pi)) Q q ∧
      |localAngle n θ q| ≤ 10*Real.pi*n/((q.den:ℝ)*Q) ∧
      (q.den = 1 → q = 0 ∨ q = 1) ∧
      (q.den = 5 → (6/5:ℝ) ≤ |localAngle n θ q| ∧
        SmoothedPhase.smoothedModulus (113/40000) τ (localAngle n θ q) <
          PhaseIntegral.radialR τ-(31:ℝ)/3125) := by
  obtain ⟨q,hmem,hq,hu,h1,h5⟩ := exists_outer_candidate n Q (6/5) θ hn hQ (by norm_num) hθ
  exact ⟨q,hmem,hq,hu,h1,fun hb => ⟨h5 hb,
    denominator_five_modulus n Q τ θ hn hQ hτ0 hτ1 hθ q hq hb⟩⟩

end
end Borwein.OuterResonantGap
