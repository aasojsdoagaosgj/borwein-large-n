import Borwein.CertifiedBulkMoments
import Borwein.BulkRationalCertificate

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Borwein.BulkCertificateCast
noncomputable section
open BulkCandidateData CertifiedBulkMoments CertifiedPhaseLower CertifiedMomentTable

def P (i : Fin 32) : ℝ := (p[i.val]!:ℝ)/PS
def R (i : Fin 32) : ℝ := (r[i.val]!:ℝ)
def B (i : Fin 32) : ℝ := (b[i.val]!:ℝ)/BS

theorem parameter_casts (i : Fin 32) :
    (BulkRationalCertificate.rv i:ℝ) = vLower i ∧
    (BulkRationalCertificate.rw3 i:ℝ) = w3Upper i ∧
    (BulkRationalCertificate.rw4 i:ℝ) = w4Upper i ∧
    (BulkRationalCertificate.rq i:ℝ) = qHi i ∧
    (BulkRationalCertificate.rql i:ℝ) = qLo i ∧
    (BulkRationalCertificate.rz i:ℝ) = tauHi i+2/5 ∧
    (BulkRationalCertificate.rp i:ℝ) = P i ∧
    (BulkRationalCertificate.rb i:ℝ) = B i := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    dsimp [BulkRationalCertificate.rv,BulkRationalCertificate.rw3,BulkRationalCertificate.rw4,
      BulkRationalCertificate.rq,BulkRationalCertificate.rql,BulkRationalCertificate.rz,
      BulkRationalCertificate.rp,BulkRationalCertificate.rb,vLower,w3Upper,w4Upper,qHi,qLo,tauHi,P,B]
    push_cast
    <;> rfl

theorem relative_cast (i : Fin 32) :
    (BulkRationalCertificate.relative i:ℝ) =
      RationalMainBudget.relative (vLower i) (w3Upper i) (w4Upper i) (tauHi i+2/5) := by
  have h := parameter_casts i
  unfold BulkRationalCertificate.relative
  push_cast
  rw [h.1,h.2.1,h.2.2.1,h.2.2.2.2.2.1]
  rfl

theorem absolute_cast (i : Fin 32) :
    (BulkRationalCertificate.absolute i:ℝ) =
      RationalMainBudget.absolute (vLower i) (w3Upper i) (qHi i) (tauHi i+2/5) := by
  have h := parameter_casts i
  unfold BulkRationalCertificate.absolute BulkRationalCertificate.aOne BulkRationalCertificate.aTwo
  push_cast
  rw [h.1,h.2.1,h.2.2.2.1,h.2.2.2.2.2.1]
  rfl

theorem checks (i : Fin 32) :
    0 < P i ∧ R i < 31147 ∧
    RationalMainBudget.relative (vLower i) (w3Upper i) (w4Upper i) (tauHi i+2/5) ≤ R i ∧
    RationalMainBudget.absolute (vLower i) (w3Upper i) (qHi i) (tauHi i+2/5) ≤ B i ∧
    P i ≤ bound 3 i ∧ B i+31147*(9/100000:ℝ) < (31147-R i)*P i := by
  have h := BulkRationalCertificate.checks i
  have hc := parameter_casts i
  have hp : 0 < P i := div_pos (by exact_mod_cast h.1) (by norm_num [PS])
  have hr : R i < 31147 := by unfold R; exact_mod_cast h.2.1
  have hrel := (Rat.cast_le (K := ℝ)).mpr h.2.2.1
  have hab := (Rat.cast_le (K := ℝ)).mpr h.2.2.2.1
  have hphase := (Rat.cast_le (K := ℝ)).mpr h.2.2.2.2.1
  have hmargin := (Rat.cast_lt (K := ℝ)).mpr h.2.2.2.2.2
  push_cast at hrel hphase hmargin
  change (BulkRationalCertificate.relative i:ℝ) ≤ R i at hrel
  change (BulkRationalCertificate.rb i:ℝ)+31147*(9/100000:ℝ) <
    (31147-R i)*(BulkRationalCertificate.rp i:ℝ) at hmargin
  rw [relative_cast] at hrel
  rw [absolute_cast,hc.2.2.2.2.2.2.2] at hab
  rw [hc.2.2.2.2.2.2.1,hc.2.2.2.2.1,hc.2.2.2.1] at hphase
  rw [hc.2.2.2.2.2.2.2,hc.2.2.2.2.2.2.1] at hmargin
  exact ⟨hp,hr,hrel,hab,by simpa [bound] using hphase,hmargin⟩

theorem bound_three_le (a : ℕ) (i : Fin 32) : bound 3 i ≤ bound a i := by
  have h := q_bounds i (tauLo i) le_rfl (by dsimp [tauLo,tauHi]; linarith)
  have hq := h.1.trans h.2
  have hl := (qLo_pos i).le
  have hu := qHi_nonneg i
  have ht0 : 0 ≤ qLo i/(1+qHi i) := div_nonneg hl (by positivity)
  have ht1 : qLo i/(1+qHi i) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have he : bound 3 i = (7/10:ℝ)*(qLo i/(1+qHi i)) := by simp [bound]
  rw [he]
  unfold bound
  split_ifs <;> nlinarith

end
end Borwein.BulkCertificateCast
