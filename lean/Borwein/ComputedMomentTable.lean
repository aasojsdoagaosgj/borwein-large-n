import Borwein.CertifiedMomentTable
import Borwein.RoundedMomentArithmetic

set_option autoImplicit false

namespace Borwein.ComputedMomentTable
noncomputable section
open CertifiedMomentTable MomentIntegralTable RoundedMomentArithmetic
open MomentExponentData ActualPhaseTaylor

def E : ℕ := 1000000000
def lowerCell (i : Fin 32) (j : ℕ) : ℕ :=
  E*D*num D lo[(i.val+1)*(j+1)]!/(den D hi[i.val*j]!)^2
def upperCell (i : Fin 32) (j : ℕ) : ℕ :=
  E*D*num D hi[i.val*j]!/(den D lo[(i.val+1)*(j+1)]!)^2+1
def lowerTotal (k : ℕ) (i : Fin 32) : ℕ := total k 64 (lowerCell i)
def upperTotal (k : ℕ) (i : Fin 32) : ℕ := total k 64 (upperCell i)
def lowerBound (k : ℕ) (i : Fin 32) : ℝ :=
  (lowerTotal k i:ℝ)/((E:ℝ)*((k:ℝ)+1)*64^(k+1))
def upperBound (k : ℕ) (i : Fin 32) : ℝ :=
  (upperTotal k i:ℝ)/((E:ℝ)*((k:ℝ)+1)*64^(k+1))

theorem upper_div (a b : ℕ) (hb : 0 < b) : a ≤ (a/b+1)*b := by
  have hr := Nat.mod_lt a hb
  have he := Nat.div_add_mod a b
  nlinarith

theorem lower_cell (i : Fin 32) (j : ℕ) :
    (lowerCell i j:ℝ)/E ≤ varianceLo i j := by
  apply checked_lower D E _ _ _ (by norm_num [D]) (by norm_num [E])
  exact Nat.div_mul_le_self _ _

theorem upper_cell (i : Fin 32) (j : ℕ) :
    varianceHi i j ≤ (upperCell i j:ℝ)/E := by
  apply checked_upper D E _ _ _ (by norm_num [D]) (by norm_num [E])
  exact upper_div _ _ (pow_pos (den_pos D _ (by norm_num [D])) 2)

theorem cell_bounds (i : Fin 32) (τ : ℝ) (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) (k : ℕ) :
    certificate k 64 (fun j => (lowerCell i j:ℝ)/E) ≤ W k τ ∧
      W k τ ≤ certificate k 64 (fun j => (upperCell i j:ℝ)/E) := by
  apply rectangle_certificate k 64 (by norm_num) (tauLo i) (tauHi i) τ
    (by unfold tauLo; positivity) hL hU (expLo i) (expHi i)
    (fun j => (lowerCell i j:ℝ)/E) (fun j => (upperCell i j:ℝ)/E)
  · intro j _
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro j hj
    have h := (CertifiedMomentExponent.rectangle_endpoints i ⟨j,hj⟩).1
    simpa only [expLo,tauHi,grid,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using h
  · intro j hj
    have h := (CertifiedMomentExponent.rectangle_endpoints i ⟨j,hj⟩).2
    simpa only [expHi,tauLo,grid,Nat.cast_ofNat] using h
  · intro j _
    exact lower_cell i j
  · intro j _
    exact upper_cell i j

theorem computed_bounds (i : Fin 32) (τ : ℝ) (hL : tauLo i ≤ τ) (hU : τ ≤ tauHi i) (k : ℕ) :
    lowerBound k i ≤ W k τ ∧ W k τ ≤ upperBound k i := by
  have h := cell_bounds i τ hL hU k
  rw [certificate_integer_sum,certificate_integer_sum] at h
  exact h

theorem all_tau_moments (τ : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) :
    ∃ i : Fin 32, tauLo i ≤ τ ∧ τ ≤ tauHi i ∧
      lowerBound 2 i ≤ RadialDerivatives.secondDerivative τ ∧
      W 3 τ ≤ upperBound 3 i ∧ W 4 τ ≤ upperBound 4 i := by
  obtain ⟨i,hi⟩ := cell_cover τ hτ hT
  exact ⟨i,hi.1,hi.2,(computed_bounds i τ hi.1 hi.2 2).1,
    (computed_bounds i τ hi.1 hi.2 3).2,(computed_bounds i τ hi.1 hi.2 4).2⟩

end
end Borwein.ComputedMomentTable
