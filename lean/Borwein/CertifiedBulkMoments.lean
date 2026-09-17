import Borwein.BulkMomentChunk00
import Borwein.BulkMomentChunk01
import Borwein.BulkMomentChunk02
import Borwein.BulkMomentChunk03
import Borwein.BulkMomentChunk04
import Borwein.BulkMomentChunk05
import Borwein.BulkMomentChunk06
import Borwein.BulkMomentChunk07
import Borwein.BulkMomentChunk08
import Borwein.BulkMomentChunk09
import Borwein.BulkMomentChunk10
import Borwein.BulkMomentChunk11
import Borwein.BulkMomentChunk12
import Borwein.BulkMomentChunk13
import Borwein.BulkMomentChunk14
import Borwein.BulkMomentChunk15
import Borwein.BulkMomentChunk16
import Borwein.BulkMomentChunk17
import Borwein.BulkMomentChunk18
import Borwein.BulkMomentChunk19
import Borwein.BulkMomentChunk20
import Borwein.BulkMomentChunk21
import Borwein.BulkMomentChunk22
import Borwein.BulkMomentChunk23
import Borwein.BulkMomentChunk24
import Borwein.BulkMomentChunk25
import Borwein.BulkMomentChunk26
import Borwein.BulkMomentChunk27
import Borwein.BulkMomentChunk28
import Borwein.BulkMomentChunk29
import Borwein.BulkMomentChunk30
import Borwein.BulkMomentChunk31

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Borwein.CertifiedBulkMoments
noncomputable section
open BulkCandidateData ComputedMomentTable CertifiedMomentTable ActualPhaseTaylor

attribute [local irreducible] ComputedMomentTable.lowerTotal ComputedMomentTable.upperTotal

def vLower (i : Fin 32) : ℝ := (v[i.val]!:ℝ)/S
def w3Upper (i : Fin 32) : ℝ := (w3[i.val]!:ℝ)/S
def w4Upper (i : Fin 32) : ℝ := (w4[i.val]!:ℝ)/S

theorem checks (i : Fin 32) :
    v[i.val]!*E*3*64^3 ≤ S*lowerTotal 2 i ∧
    S*upperTotal 3 i ≤ w3[i.val]!*E*4*64^4 ∧
    S*upperTotal 4 i ≤ w4[i.val]!*E*5*64^5 := by
  rcases i with ⟨j,hj⟩
  interval_cases j
  · have he : (⟨0,hj⟩:Fin 32) = (0:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((0:Fin 32):ℕ) = 0 by rfl]
    with_reducible exact ⟨BulkMomentChunk00.variance_lower,BulkMomentChunk00.third_upper,BulkMomentChunk00.fourth_upper⟩
  · have he : (⟨1,hj⟩:Fin 32) = (1:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((1:Fin 32):ℕ) = 1 by rfl]
    with_reducible exact ⟨BulkMomentChunk01.variance_lower,BulkMomentChunk01.third_upper,BulkMomentChunk01.fourth_upper⟩
  · have he : (⟨2,hj⟩:Fin 32) = (2:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((2:Fin 32):ℕ) = 2 by rfl]
    with_reducible exact ⟨BulkMomentChunk02.variance_lower,BulkMomentChunk02.third_upper,BulkMomentChunk02.fourth_upper⟩
  · have he : (⟨3,hj⟩:Fin 32) = (3:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((3:Fin 32):ℕ) = 3 by rfl]
    with_reducible exact ⟨BulkMomentChunk03.variance_lower,BulkMomentChunk03.third_upper,BulkMomentChunk03.fourth_upper⟩
  · have he : (⟨4,hj⟩:Fin 32) = (4:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((4:Fin 32):ℕ) = 4 by rfl]
    with_reducible exact ⟨BulkMomentChunk04.variance_lower,BulkMomentChunk04.third_upper,BulkMomentChunk04.fourth_upper⟩
  · have he : (⟨5,hj⟩:Fin 32) = (5:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((5:Fin 32):ℕ) = 5 by rfl]
    with_reducible exact ⟨BulkMomentChunk05.variance_lower,BulkMomentChunk05.third_upper,BulkMomentChunk05.fourth_upper⟩
  · have he : (⟨6,hj⟩:Fin 32) = (6:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((6:Fin 32):ℕ) = 6 by rfl]
    with_reducible exact ⟨BulkMomentChunk06.variance_lower,BulkMomentChunk06.third_upper,BulkMomentChunk06.fourth_upper⟩
  · have he : (⟨7,hj⟩:Fin 32) = (7:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((7:Fin 32):ℕ) = 7 by rfl]
    with_reducible exact ⟨BulkMomentChunk07.variance_lower,BulkMomentChunk07.third_upper,BulkMomentChunk07.fourth_upper⟩
  · have he : (⟨8,hj⟩:Fin 32) = (8:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((8:Fin 32):ℕ) = 8 by rfl]
    with_reducible exact ⟨BulkMomentChunk08.variance_lower,BulkMomentChunk08.third_upper,BulkMomentChunk08.fourth_upper⟩
  · have he : (⟨9,hj⟩:Fin 32) = (9:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((9:Fin 32):ℕ) = 9 by rfl]
    with_reducible exact ⟨BulkMomentChunk09.variance_lower,BulkMomentChunk09.third_upper,BulkMomentChunk09.fourth_upper⟩
  · have he : (⟨10,hj⟩:Fin 32) = (10:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((10:Fin 32):ℕ) = 10 by rfl]
    with_reducible exact ⟨BulkMomentChunk10.variance_lower,BulkMomentChunk10.third_upper,BulkMomentChunk10.fourth_upper⟩
  · have he : (⟨11,hj⟩:Fin 32) = (11:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((11:Fin 32):ℕ) = 11 by rfl]
    with_reducible exact ⟨BulkMomentChunk11.variance_lower,BulkMomentChunk11.third_upper,BulkMomentChunk11.fourth_upper⟩
  · have he : (⟨12,hj⟩:Fin 32) = (12:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((12:Fin 32):ℕ) = 12 by rfl]
    with_reducible exact ⟨BulkMomentChunk12.variance_lower,BulkMomentChunk12.third_upper,BulkMomentChunk12.fourth_upper⟩
  · have he : (⟨13,hj⟩:Fin 32) = (13:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((13:Fin 32):ℕ) = 13 by rfl]
    with_reducible exact ⟨BulkMomentChunk13.variance_lower,BulkMomentChunk13.third_upper,BulkMomentChunk13.fourth_upper⟩
  · have he : (⟨14,hj⟩:Fin 32) = (14:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((14:Fin 32):ℕ) = 14 by rfl]
    with_reducible exact ⟨BulkMomentChunk14.variance_lower,BulkMomentChunk14.third_upper,BulkMomentChunk14.fourth_upper⟩
  · have he : (⟨15,hj⟩:Fin 32) = (15:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((15:Fin 32):ℕ) = 15 by rfl]
    with_reducible exact ⟨BulkMomentChunk15.variance_lower,BulkMomentChunk15.third_upper,BulkMomentChunk15.fourth_upper⟩
  · have he : (⟨16,hj⟩:Fin 32) = (16:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((16:Fin 32):ℕ) = 16 by rfl]
    with_reducible exact ⟨BulkMomentChunk16.variance_lower,BulkMomentChunk16.third_upper,BulkMomentChunk16.fourth_upper⟩
  · have he : (⟨17,hj⟩:Fin 32) = (17:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((17:Fin 32):ℕ) = 17 by rfl]
    with_reducible exact ⟨BulkMomentChunk17.variance_lower,BulkMomentChunk17.third_upper,BulkMomentChunk17.fourth_upper⟩
  · have he : (⟨18,hj⟩:Fin 32) = (18:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((18:Fin 32):ℕ) = 18 by rfl]
    with_reducible exact ⟨BulkMomentChunk18.variance_lower,BulkMomentChunk18.third_upper,BulkMomentChunk18.fourth_upper⟩
  · have he : (⟨19,hj⟩:Fin 32) = (19:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((19:Fin 32):ℕ) = 19 by rfl]
    with_reducible exact ⟨BulkMomentChunk19.variance_lower,BulkMomentChunk19.third_upper,BulkMomentChunk19.fourth_upper⟩
  · have he : (⟨20,hj⟩:Fin 32) = (20:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((20:Fin 32):ℕ) = 20 by rfl]
    with_reducible exact ⟨BulkMomentChunk20.variance_lower,BulkMomentChunk20.third_upper,BulkMomentChunk20.fourth_upper⟩
  · have he : (⟨21,hj⟩:Fin 32) = (21:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((21:Fin 32):ℕ) = 21 by rfl]
    with_reducible exact ⟨BulkMomentChunk21.variance_lower,BulkMomentChunk21.third_upper,BulkMomentChunk21.fourth_upper⟩
  · have he : (⟨22,hj⟩:Fin 32) = (22:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((22:Fin 32):ℕ) = 22 by rfl]
    with_reducible exact ⟨BulkMomentChunk22.variance_lower,BulkMomentChunk22.third_upper,BulkMomentChunk22.fourth_upper⟩
  · have he : (⟨23,hj⟩:Fin 32) = (23:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((23:Fin 32):ℕ) = 23 by rfl]
    with_reducible exact ⟨BulkMomentChunk23.variance_lower,BulkMomentChunk23.third_upper,BulkMomentChunk23.fourth_upper⟩
  · have he : (⟨24,hj⟩:Fin 32) = (24:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((24:Fin 32):ℕ) = 24 by rfl]
    with_reducible exact ⟨BulkMomentChunk24.variance_lower,BulkMomentChunk24.third_upper,BulkMomentChunk24.fourth_upper⟩
  · have he : (⟨25,hj⟩:Fin 32) = (25:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((25:Fin 32):ℕ) = 25 by rfl]
    with_reducible exact ⟨BulkMomentChunk25.variance_lower,BulkMomentChunk25.third_upper,BulkMomentChunk25.fourth_upper⟩
  · have he : (⟨26,hj⟩:Fin 32) = (26:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((26:Fin 32):ℕ) = 26 by rfl]
    with_reducible exact ⟨BulkMomentChunk26.variance_lower,BulkMomentChunk26.third_upper,BulkMomentChunk26.fourth_upper⟩
  · have he : (⟨27,hj⟩:Fin 32) = (27:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((27:Fin 32):ℕ) = 27 by rfl]
    with_reducible exact ⟨BulkMomentChunk27.variance_lower,BulkMomentChunk27.third_upper,BulkMomentChunk27.fourth_upper⟩
  · have he : (⟨28,hj⟩:Fin 32) = (28:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((28:Fin 32):ℕ) = 28 by rfl]
    with_reducible exact ⟨BulkMomentChunk28.variance_lower,BulkMomentChunk28.third_upper,BulkMomentChunk28.fourth_upper⟩
  · have he : (⟨29,hj⟩:Fin 32) = (29:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((29:Fin 32):ℕ) = 29 by rfl]
    with_reducible exact ⟨BulkMomentChunk29.variance_lower,BulkMomentChunk29.third_upper,BulkMomentChunk29.fourth_upper⟩
  · have he : (⟨30,hj⟩:Fin 32) = (30:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((30:Fin 32):ℕ) = 30 by rfl]
    with_reducible exact ⟨BulkMomentChunk30.variance_lower,BulkMomentChunk30.third_upper,BulkMomentChunk30.fourth_upper⟩
  · have he : (⟨31,hj⟩:Fin 32) = (31:Fin 32) := by apply Fin.ext; rfl
    rw [he]
    simp only [show ((31:Fin 32):ℕ) = 31 by rfl]
    with_reducible exact ⟨BulkMomentChunk31.variance_lower,BulkMomentChunk31.third_upper,BulkMomentChunk31.fourth_upper⟩

theorem lower_round (k s c : ℕ) (i : Fin 32) (hs : 0 < s)
    (h : c*E*(k+1)*64^(k+1) ≤ s*lowerTotal k i) :
    (c:ℝ)/s ≤ lowerBound k i := by
  unfold lowerBound
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hd : (0:ℝ) < (E:ℝ)*((k:ℝ)+1)*64^(k+1) := by unfold E; positivity
  apply (div_le_div_iff₀ hs' hd).mpr
  have hr : ((c*E*(k+1)*64^(k+1):ℕ):ℝ) ≤ ((s*lowerTotal k i:ℕ):ℝ) := by exact_mod_cast h
  push_cast at hr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hr

theorem upper_round (k s c : ℕ) (i : Fin 32) (hs : 0 < s)
    (h : s*upperTotal k i ≤ c*E*(k+1)*64^(k+1)) :
    upperBound k i ≤ (c:ℝ)/s := by
  unfold upperBound
  have hs' : (0:ℝ) < s := by exact_mod_cast hs
  have hd : (0:ℝ) < (E:ℝ)*((k:ℝ)+1)*64^(k+1) := by unfold E; positivity
  apply (div_le_div_iff₀ hd hs').mpr
  have hr : ((s*upperTotal k i:ℕ):ℝ) ≤ ((c*E*(k+1)*64^(k+1):ℕ):ℝ) := by exact_mod_cast h
  push_cast at hr
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hr

theorem v_positive (i : Fin 32) : 0 < vLower i := by
  have h : 0 < v[i.val]! := by revert i; decide +kernel
  exact div_pos (by exact_mod_cast h) (by norm_num [S])

theorem actual_bounds (i : Fin 32) (τ : ℝ) (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) :
    vLower i ≤ RadialDerivatives.secondDerivative τ ∧
      W 3 τ ≤ w3Upper i ∧ W 4 τ ≤ w4Upper i := by
  have h := checks i
  exact ⟨(lower_round 2 S (v[i.val]!) i (by norm_num [S]) h.1).trans
      (computed_bounds i τ hL hU 2).1,
    (computed_bounds i τ hL hU 3).2.trans
      (upper_round 3 S (w3[i.val]!) i (by norm_num [S]) h.2.1),
    (computed_bounds i τ hL hU 4).2.trans
      (upper_round 4 S (w4[i.val]!) i (by norm_num [S]) h.2.2)⟩

end
end Borwein.CertifiedBulkMoments
