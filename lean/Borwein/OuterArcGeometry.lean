import Borwein.CompactCuspCover
import Borwein.WideGapIntegral

namespace Borwein.OuterArcGeometry
noncomputable section
open Set (Icc)
open SaddleArcConnection DirichletCover

def region (n : ℕ) (h θ : ℝ) : Prop :=
  θ ∈ Icc 0 (center 0-h/(5*n)) ∨
  θ ∈ Icc (center 0+h/(5*n)) (center 1-h/(5*n)) ∨
  θ ∈ Icc (center 1+h/(5*n)) (center 2-h/(5*n)) ∨
  θ ∈ Icc (center 2+h/(5*n)) (center 3-h/(5*n)) ∨
  θ ∈ Icc (center 3+h/(5*n)) (2*Real.pi)

theorem region_in_circle (n : ℕ) (h θ : ℝ) (hh : 0 ≤ h) (hθ : region n h θ) :
    θ ∈ Icc (0:ℝ) (2*Real.pi) := by
  have hd : 0 ≤ h/(5*(n:ℝ)) := by positivity
  rcases hθ with hθ | hθ | hθ | hθ | hθ
  all_goals
    norm_num [center] at hθ
    constructor <;> linarith [hθ.1,hθ.2,Real.pi_pos]

theorem root_distance (n : ℕ) (h θ : ℝ) (hh : 0 ≤ h) (hθ : region n h θ) (j : Fin 4) :
    h/(5*(n:ℝ)) ≤ |θ-center j| := by
  have hd : 0 ≤ h/(5*(n:ℝ)) := by positivity
  rcases hθ with hθ | hθ | hθ | hθ | hθ
  all_goals
    rcases hθ with ⟨hl,hr⟩
    fin_cases j <;> norm_num [center] at *
    all_goals
      apply le_abs.mpr
      first | left; linarith [Real.pi_pos] | right; linarith [Real.pi_pos]

theorem normalized_angle (n : ℕ) (h θ : ℝ) (hh : 0 ≤ h) (hθ : region n h θ) :
    θ/(2*Real.pi) ∈ Icc (0:ℝ) 1 := by
  have hc := region_in_circle n h θ hh hθ
  exact ⟨div_nonneg hc.1 (by positivity),(div_le_one (by positivity)).mpr hc.2⟩

theorem denominator_five_local_lower (n Q : ℕ) (h θ : ℝ) (hn : 0 < n)
    (hQ : 2 ≤ Q) (hh : 0 ≤ h) (hθ : region n h θ) (q : ℚ)
    (hq : Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5) : h ≤ |localAngle n θ q| := by
  obtain ⟨j,hj⟩ := CompactCuspCover.denominator_five (θ/(2*Real.pi)) Q hQ q hq
    (normalized_angle n h θ hh hθ) hb
  have hc : 2*Real.pi*(q:ℝ) = center j := by
    rw [hj]
    push_cast
    unfold center
    ring
  have hn0 : 0 < 5*(n:ℝ) := by positivity
  have hd := (div_le_iff₀ hn0).mp (root_distance n h θ hh hθ j)
  rw [localAngle,hc,abs_mul,abs_of_pos hn0]
  nlinarith

theorem exists_outer_candidate (n Q : ℕ) (h θ : ℝ) (hn : 0 < n)
    (hQ : 2 ≤ Q) (hh : 0 ≤ h) (hθ : region n h θ) :
    ∃ q ∈ CompactCuspCover.candidates Q,
      Near (θ/(2*Real.pi)) Q q ∧
      |localAngle n θ q| ≤ 10*Real.pi*n/((q.den:ℝ)*Q) ∧
      (q.den = 1 → q = 0 ∨ q = 1) ∧
      (q.den = 5 → h ≤ |localAngle n θ q|) := by
  have hξ := normalized_angle n h θ hh hθ
  obtain ⟨q,hmem,hq⟩ := CompactCuspCover.exists_candidate (θ/(2*Real.pi)) Q hQ hξ
  exact ⟨q,hmem,hq,localAngle_bound n Q θ q hq,
    CompactCuspCover.denominator_one _ Q hQ q hq hξ,
    denominator_five_local_lower n Q h θ hn hQ hh hθ q hq⟩

end
end Borwein.OuterArcGeometry
