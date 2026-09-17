import Borwein.RoundedWeight
import Borwein.RoundedWeightChecks

namespace Borwein.CheckedWeights
noncomputable section
open Borwein.GroupedWeights Borwein.ResonantCertificate Borwein.SmoothedCertificate

theorem all_weight_bounds (d : Fin 4) (i : ℕ) (hi : i < 400) :
    (RoundedWeightData.lo d i:ℝ)/RoundedWeightData.W ≤
      envelope d ((113/40000:ℝ)+(11/2:ℝ)*((i+1:ℕ):ℝ)/400) ∧
    envelope d ((113/40000:ℝ)+(11/2:ℝ)*((i+1:ℕ):ℝ)/400) ≤
      (RoundedWeightData.hi d i:ℝ)/RoundedWeightData.W :=
  RoundedWeight.checker_sound d i hi (RoundedWeightChecks.all_checks d i hi)

def lower (d : Fin 4) (i : ℕ) : ℝ := (RoundedWeightData.lo d i:ℝ)/RoundedWeightData.W
def upper (d : Fin 4) (i : ℕ) : ℝ := (RoundedWeightData.hi d i:ℝ)/RoundedWeightData.W

set_option maxRecDepth 16384 in
theorem terminal_values : ∀ d : Fin 4,
    RoundedWeightData.lo d 400 = 0 ∧ RoundedWeightData.hi d 400 = 0 := by decide

theorem height_bounds (d : Fin 4) (i : ℕ) (hi : i ≤ 400) :
    lower d i ≤ shiftedHeights (uniformGrid 400) 400 (113/40000) (11/2) d i ∧
    shiftedHeights (uniformGrid 400) 400 (113/40000) (11/2) d i ≤ upper d i := by
  rcases lt_or_eq_of_le hi with h | rfl
  · simpa only [lower, upper, shiftedHeights, if_pos h, uniformGrid,
      Nat.cast_ofNat, mul_div_assoc] using all_weight_bounds d i h
  · simp only [lower, upper, shiftedHeights, lt_self_iff_false, if_false,
      (terminal_values d).1, (terminal_values d).2, Nat.cast_zero, zero_div, le_refl, and_self]

def lowerGap := Borwein.FiniteGapBounds.lowerCertificate lower upper (uniformGrid 400) 400 (6/5)

theorem lowerGap_le : lowerGap ≤ uniformGap (113/40000) (11/2) (6/5) 400 := by
  apply Borwein.FiniteGapBounds.lowerCertificate_le _ _ _ _ _ _ (by norm_num)
  · intro i _
    unfold uniformGrid
    positivity
  · exact fun d i hi => (height_bounds d i (Nat.le_of_lt hi)).1
  · exact fun d i hi => (height_bounds d i hi).2

theorem modulus_upper (τ t : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (ht : 6/5 ≤ |t|) :
    Borwein.SmoothedPhase.smoothedModulus (113/40000) τ t ≤
      Borwein.PhaseIntegral.radialR τ-lowerGap := by
  have h := current_parameters_upper τ t hτ hT ht
  have hl := lowerGap_le
  linarith

end
end Borwein.CheckedWeights

