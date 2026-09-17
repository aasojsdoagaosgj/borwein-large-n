import Borwein.BulkCandidateData
import Borwein.RationalMainBudget
import Borwein.CertifiedPhaseLower

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Borwein.BulkRationalCertificate
open BulkCandidateData

def rv (i : Fin 32) : ℚ := (v[i.val]!:ℚ)/S
def rw3 (i : Fin 32) : ℚ := (w3[i.val]!:ℚ)/S
def rw4 (i : Fin 32) : ℚ := (w4[i.val]!:ℚ)/S
def rq (i : Fin 32) : ℚ := (MomentExponentData.hi[64*i.val]!:ℚ)/MomentExponentData.D
def rql (i : Fin 32) : ℚ := (MomentExponentData.lo[64*(i.val+1)]!:ℚ)/MomentExponentData.D
def rz (i : Fin 32) : ℚ := 11*((i.val:ℚ)+1)/64+2/5
def rp (i : Fin 32) : ℚ := (p[i.val]!:ℚ)/PS
def rb (i : Fin 32) : ℚ := (b[i.val]!:ℚ)/BS
def aOne (q : ℚ) : ℚ := (77/50)*(16/15)*q
def aTwo (q : ℚ) : ℚ := (77/100)*((64/45)*q+((16/15)*q)^2)
def relative (i : Fin 32) : ℚ :=
  (240*rw4 i/(32*(39/100:ℚ)^2*(rv i)^2)+
    2645*(rw3 i)^2/(192*(39/100:ℚ)^3*(rv i)^3)+rz i/30)/(22/25)
def absolute (i : Fin 32) : ℚ :=
  (4*(23*aOne (rq i)*rw3 i/(8*(39/100:ℚ)^2*(rv i)^2)+
      aTwo (rq i)/(2*(39/100:ℚ)*rv i))+
    rz i/30*((8/5:ℚ)*aOne (rq i))+(1232/1875:ℚ)*rz i*rq i)/(22/25)
def Checks (i : Fin 32) : Prop :=
  0 < p[i.val]! ∧ r[i.val]! < 31147 ∧ relative i ≤ (r[i.val]!:ℚ) ∧
  absolute i ≤ rb i ∧ rp i ≤ (7/10:ℚ)*(rql i/(1+rq i)) ∧
  rb i+31147*(9/100000:ℚ) < (31147-(r[i.val]!:ℚ))*rp i

instance (i : Fin 32) : Decidable (Checks i) := by
  unfold Checks
  infer_instance

theorem block0 (j : Fin 8) : Checks ⟨0+j.val,by omega⟩ := by
  revert j
  decide +kernel

theorem block1 (j : Fin 8) : Checks ⟨8+j.val,by omega⟩ := by
  revert j
  decide +kernel

theorem block2 (j : Fin 8) : Checks ⟨16+j.val,by omega⟩ := by
  revert j
  decide +kernel

theorem block3 (j : Fin 8) : Checks ⟨24+j.val,by omega⟩ := by
  revert j
  decide +kernel

theorem block_checks (b : Fin 4) (j : Fin 8) : Checks ⟨8*b.val+j.val,by omega⟩ := by
  fin_cases b
  · exact block0 j
  · exact block1 j
  · exact block2 j
  · exact block3 j

theorem checks (i : Fin 32) : Checks i := by
  have h := block_checks ⟨i.val/8,by omega⟩ ⟨i.val%8,Nat.mod_lt _ (by norm_num)⟩
  have he : (⟨8*(i.val/8)+i.val%8,by omega⟩:Fin 32) = i := by
    apply Fin.ext
    dsimp
    omega
  simpa only [he] using h

end Borwein.BulkRationalCertificate
