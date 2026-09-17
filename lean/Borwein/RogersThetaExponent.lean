import Borwein.CiglerWeights
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false

namespace Borwein.RogersThetaExponent
noncomputable section
open Complex CiglerWeights

def exponent (a : ℕ) (j : ℤ) : ℤ := (pentagonal j:ℤ)+j*j+2*(a:ℤ)*j
def degree (a : ℕ) (j : ℤ) : ℕ := (exponent a j).toNat
def thetaTerm (q : ℂ) (a : ℕ) (j : ℤ) : ℂ := weight q j*q^(j*j+2*(a:ℤ)*j)

theorem twice_exponent (a : ℕ) (j : ℤ) :
    2*exponent a j=j*(5*j-1+4*(a:ℤ)) := by
  unfold exponent
  nlinarith [two_mul_natCast_pentagonal j]

theorem exponent_nonneg (a : ℕ) (ha : a ≤ 1) (j : ℤ) : 0 ≤ exponent a j := by
  have he := twice_exponent a j
  have ha' : a=0 ∨ a=1 := by omega
  have hj : j ≤ 0 ∨ 1 ≤ j := by omega
  rcases ha' with rfl | rfl <;> norm_num at he <;> rcases hj with hj | hj
  · nlinarith [mul_nonneg (show 0 ≤ -j by omega) (show 0 ≤ 1-j by omega)]
  · nlinarith [mul_nonneg (show 0 ≤ j by omega) (show 0 ≤ j-1 by omega)]
  · by_cases hz : j=0
    · subst j; norm_num [exponent]
    · nlinarith [mul_nonneg (show 0 ≤ -j by omega) (show 0 ≤ -j-1 by omega)]
  · nlinarith [sq_nonneg j]

theorem degree_cast (a : ℕ) (ha : a ≤ 1) (j : ℤ) : (degree a j:ℤ)=exponent a j := by
  exact Int.toNat_of_nonneg (exponent_nonneg a ha j)

theorem degree_injective (a : ℕ) (ha : a ≤ 1) : Function.Injective (degree a) := by
  intro i j hij
  have he : exponent a i=exponent a j := by
    rw [← degree_cast a ha i, ← degree_cast a ha j, hij]
  have hf : (i-j)*(5*(i+j)-1+4*(a:ℤ))=0 := by
    nlinarith [twice_exponent a i, twice_exponent a j]
  have hn : 5*(i+j)-1+4*(a:ℤ) ≠ 0 := by
    have ha' : (a:ℤ) ≤ 1 := by exact_mod_cast ha
    omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hn)

theorem term_as_power (q : ℂ) (hq0 : q ≠ 0) (a : ℕ) (ha : a ≤ 1) (j : ℤ) :
    thetaTerm q a j=(-1:ℂ)^j*q^(degree a j) := by
  unfold thetaTerm weight
  rw [mul_assoc, ← zpow_add₀ hq0]
  rw [show (pentagonal j:ℤ)+(j*j+2*(a:ℤ)*j)=exponent a j by unfold exponent; ring]
  rw [← degree_cast a ha j, zpow_natCast]

theorem term_norm (q : ℂ) (hq0 : q ≠ 0) (a : ℕ) (ha : a ≤ 1) (j : ℤ) :
    ‖thetaTerm q a j‖=‖q‖^(degree a j) := by
  rw [term_as_power q hq0 a ha j]
  simp

theorem majorant_summable (q : ℂ) (hq : ‖q‖ < 1) (a : ℕ) (ha : a ≤ 1) :
    Summable (fun j : ℤ => ‖q‖^(degree a j)) := by
  simpa only [Function.comp_def] using
    (summable_geometric_of_lt_one (norm_nonneg q) hq).comp_injective (degree_injective a ha)

theorem theta_summable (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (a : ℕ) (ha : a ≤ 1) :
    Summable (thetaTerm q a) :=
  (majorant_summable q hq a ha).of_norm_bounded (fun j => (term_norm q hq0 a ha j).le)

end
end Borwein.RogersThetaExponent
