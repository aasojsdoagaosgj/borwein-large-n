import Borwein.CertifiedMomentExponent
import Borwein.MomentIntegralTable

set_option autoImplicit false

namespace Borwein.CertifiedMomentTable
noncomputable section
open MomentIntegralTable ActualPhaseTaylor

def tauLo (i : Fin 32) : ℝ := 11*(i.val:ℝ)/64
def tauHi (i : Fin 32) : ℝ := 11*((i.val:ℝ)+1)/64
def expLo (i : Fin 32) (j : ℕ) : ℝ :=
  (MomentExponentData.lo[(i.val+1)*(j+1)]!:ℝ)/MomentExponentData.D
def expHi (i : Fin 32) (j : ℕ) : ℝ :=
  (MomentExponentData.hi[i.val*j]!:ℝ)/MomentExponentData.D
def varianceLo (i : Fin 32) (j : ℕ) : ℝ :=
  VarianceInterval.numerator (expLo i j)/GroupedWeights.denominator (expHi i j)^2
def varianceHi (i : Fin 32) (j : ℕ) : ℝ :=
  VarianceInterval.numerator (expHi i j)/GroupedWeights.denominator (expLo i j)^2

theorem moment_bounds (i : Fin 32) (τ : ℝ) (hlo : tauLo i ≤ τ) (hhi : τ ≤ tauHi i) (k : ℕ) :
    certificate k 64 (varianceLo i) ≤ W k τ ∧ W k τ ≤ certificate k 64 (varianceHi i) := by
  apply rectangle_certificate k 64 (by norm_num) (tauLo i) (tauHi i) τ
    (by unfold tauLo; positivity) hlo hhi (expLo i) (expHi i) (varianceLo i) (varianceHi i)
  · intro j _
    unfold expLo
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro j hj
    have h := (CertifiedMomentExponent.rectangle_endpoints i ⟨j,hj⟩).1
    simpa only [expLo,tauHi,grid,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h
  · intro j hj
    have h := (CertifiedMomentExponent.rectangle_endpoints i ⟨j,hj⟩).2
    simpa only [expHi,tauLo,grid,Nat.cast_ofNat] using h
  · intro j _
    exact le_rfl
  · intro j _
    exact le_rfl

theorem variance_third_fourth (i : Fin 32) (τ : ℝ) (hlo : tauLo i ≤ τ) (hhi : τ ≤ tauHi i) :
    certificate 2 64 (varianceLo i) ≤ RadialDerivatives.secondDerivative τ ∧
      W 3 τ ≤ certificate 3 64 (varianceHi i) ∧ W 4 τ ≤ certificate 4 64 (varianceHi i) := by
  exact ⟨(moment_bounds i τ hlo hhi 2).1,
    (moment_bounds i τ hlo hhi 3).2,(moment_bounds i τ hlo hhi 4).2⟩

theorem cell_cover (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    ∃ i : Fin 32, tauLo i ≤ τ ∧ τ ≤ tauHi i := by
  by_cases he : τ = 11/2
  · refine ⟨31,?_⟩
    norm_num [tauLo,tauHi,he]
  · have hx0 : 0 ≤ τ*64/11 := by positivity
    have hx1 : τ*64/11 < 32 := by
      have ht : τ < 11/2 := lt_of_le_of_ne hT he
      linarith
    have hi : ⌊τ*64/11⌋₊ < 32 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hx1)
    refine ⟨⟨⌊τ*64/11⌋₊,hi⟩,?_⟩
    have hL := Nat.floor_le hx0
    have hU := Nat.lt_floor_add_one (τ*64/11)
    dsimp [tauLo,tauHi]
    constructor <;> linarith

theorem all_tau_moments (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    ∃ i : Fin 32, tauLo i ≤ τ ∧ τ ≤ tauHi i ∧
      certificate 2 64 (varianceLo i) ≤ RadialDerivatives.secondDerivative τ ∧
      W 3 τ ≤ certificate 3 64 (varianceHi i) ∧ W 4 τ ≤ certificate 4 64 (varianceHi i) := by
  obtain ⟨i,hi⟩ := cell_cover τ hτ hT
  exact ⟨i,hi.1,hi.2,variance_third_fourth i τ hi.1 hi.2⟩

end
end Borwein.CertifiedMomentTable
