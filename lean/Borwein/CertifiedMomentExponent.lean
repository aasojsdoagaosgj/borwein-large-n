import Borwein.MomentExponentChunk00
import Borwein.MomentExponentChunk01
import Borwein.MomentExponentChunk02
import Borwein.MomentExponentChunk03
import Borwein.MomentExponentChunk04
import Borwein.MomentExponentChunk05
import Borwein.MomentExponentChunk06
import Borwein.MomentExponentChunk07

set_option autoImplicit false
namespace Borwein.CertifiedMomentExponent
noncomputable section
open MomentExponentData

theorem step_bounds :
    (stepLo:ℝ)/D ≤ Real.exp (-(11/4096:ℝ)) ∧ Real.exp (-(11/4096:ℝ)) ≤ (stepHi:ℝ)/D := by
  apply ExpCertificate.exp_enclosure _ _ _ 8 (by norm_num) (by norm_num)
  all_goals norm_num [ExpCertificate.taylorSum,ExpCertificate.remainder,
    Finset.sum_range_succ,Nat.factorial,stepLo,stepHi,D]

theorem block_steps (b : Fin 8) (j : Fin 256) :
    lo[b.val*256+j.val+1]!*D ≤ lo[b.val*256+j.val]!*stepLo ∧
      hi[b.val*256+j.val]!*stepHi ≤ hi[b.val*256+j.val+1]!*D := by
  fin_cases b
  · exact MomentExponentChunk00.steps j
  · exact MomentExponentChunk01.steps j
  · exact MomentExponentChunk02.steps j
  · exact MomentExponentChunk03.steps j
  · exact MomentExponentChunk04.steps j
  · exact MomentExponentChunk05.steps j
  · exact MomentExponentChunk06.steps j
  · exact MomentExponentChunk07.steps j

theorem steps (i : ℕ) (hiN : i < 2048) :
    lo[i+1]!*D ≤ lo[i]!*stepLo ∧ hi[i]!*stepHi ≤ hi[i+1]!*D := by
  have h := block_steps ⟨i/256,by omega⟩ ⟨i%256,Nat.mod_lt _ (by norm_num)⟩
  change lo[i/256*256+i%256+1]!*D ≤ lo[i/256*256+i%256]!*stepLo ∧
    hi[i/256*256+i%256]!*stepHi ≤ hi[i/256*256+i%256+1]!*D at h
  have he : i/256*256+i%256 = i := by omega
  simpa only [he] using h

theorem all_bounds (i : ℕ) (hiN : i ≤ 2048) :
    (lo[i]!:ℝ)/D ≤ Real.exp (-(11/4096:ℝ)*(i:ℝ)) ∧
      Real.exp (-(11/4096:ℝ)*(i:ℝ)) ≤ (hi[i]!:ℝ)/D := by
  exact RoundedExponentialGrid.checked_recurrence (fun j => lo[j]!) (fun j => hi[j]!)
    D stepLo stepHi 2048 (11/4096) (by decide) step_bounds starts steps i hiN

theorem rectangle_endpoints (i : Fin 32) (j : Fin 64) :
    (lo[(i.val+1)*(j.val+1)]!:ℝ)/D ≤
      Real.exp (-(11*((i.val:ℝ)+1)/64)*(((j.val:ℝ)+1)/64)) ∧
    Real.exp (-(11*(i.val:ℝ)/64)*((j.val:ℝ)/64)) ≤ (hi[i.val*j.val]!:ℝ)/D := by
  have hL := (all_bounds ((i.val+1)*(j.val+1))
    (show (i.val+1)*(j.val+1) ≤ 2048 from
      Nat.mul_le_mul (by omega : i.val+1 ≤ 32) (by omega : j.val+1 ≤ 64))).1
  have hU := (all_bounds (i.val*j.val)
    (show i.val*j.val ≤ 2048 from
      Nat.mul_le_mul (by omega : i.val ≤ 32) (by omega : j.val ≤ 64))).2
  have hle : -(11/4096:ℝ)*(((i.val+1)*(j.val+1):ℕ):ℝ) =
      -(11*((i.val:ℝ)+1)/64)*(((j.val:ℝ)+1)/64) := by push_cast; ring
  have hue : -(11/4096:ℝ)*((i.val*j.val:ℕ):ℝ) =
      -(11*(i.val:ℝ)/64)*((j.val:ℝ)/64) := by push_cast; ring
  rw [hle] at hL
  rw [hue] at hU
  exact ⟨hL,hU⟩

end
end Borwein.CertifiedMomentExponent
