import Borwein.CuspSineChunk0
import Borwein.CuspSineChunk1
import Borwein.CuspSineChunk2
import Borwein.CuspSineChunk3
import Borwein.CuspSineChunk4
import Borwein.CuspSineChunk5
import Borwein.CuspSineChunk6
import Borwein.CuspSineChunk7

set_option autoImplicit false

namespace Borwein.CertifiedDenominatorOne
noncomputable section
open Complex CuspCellCertificate CuspSineData SmoothedResonantMain

theorem all_valid (i : Fin 160) : Valid i.val (row i) := by
  have hi : i.val/20 < 8 := by omega
  interval_cases h : i.val/20
  · exact CuspSineChunk0.valid i h
  · exact CuspSineChunk1.valid i h
  · exact CuspSineChunk2.valid i h
  · exact CuspSineChunk3.valid i h
  · exact CuspSineChunk4.valid i h
  · exact CuspSineChunk5.valid i h
  · exact CuspSineChunk6.valid i h
  · exact CuspSineChunk7.valid i h

theorem compact_gap (τ t : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1/2)
    (ht0 : 2 ≤ |t|) (ht1 : |t| ≤ 6) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 PositiveCuspCertificate.eta
      ((τ:ℂ)-(t:ℂ)*I) := by
  obtain ⟨i,hl,hu⟩ := cell_cover |t| ht0 ht1
  obtain ⟨h1,h2,h3,hE⟩ := valid_sound i (row i) (all_valid i) |t| hl hu
  have h := CuspRectangleBridge.compact_gap_from_bounds τ |t|
    ((row i).s1-1/80) ((row i).s2-2/80) ((row i).s3-3/80) hτ0 hτ1
    (by linarith) h1 h2 h3 hE
  rw [CuspRectangleBridge.pole_abs] at h
  exact h

theorem all_gap (τ t : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2) :
    (1/40:ℝ) ≤ PhaseIntegral.radialR τ-4*poleIntegral 1 PositiveCuspCertificate.eta
      ((τ:ℂ)-(t:ℂ)*I) := by
  by_cases hτ : 1/2 ≤ τ
  · exact PositiveCuspCertificate.positive_gap τ t hτ hτ1
  by_cases hs : |t| ≤ 2
  · exact SmallAngleIntegral.small_gap _ τ t (by norm_num [PositiveCuspCertificate.eta]) hτ0 (by linarith) hs
  by_cases hl : 6 ≤ |t|
  · exact LargeAnglePole.large_gap _ τ t (by norm_num [PositiveCuspCertificate.eta]) hτ0 (by linarith) hl
  exact compact_gap τ t hτ0 (by linarith) (by linarith) (by linarith)

theorem polynomial_decay (n : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 31147 ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) 4139 q) (hb : q.den = 1) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (FiniteBlockLocalization.point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-1/4000)) :=
  SmallAngleIntegral.polynomial_from_gap n τ θ q hn hτ0 hτ1 hq hb
    (all_gap τ (DirichletCover.localAngle n θ q) hτ0 hτ1)

end
end Borwein.CertifiedDenominatorOne
