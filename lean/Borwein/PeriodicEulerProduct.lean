import Borwein.PeriodicFactorLoss

set_option autoImplicit false

namespace Borwein.PeriodicEulerProduct
noncomputable section
open Complex

def exponent (j : Fin 4) (m : ℕ) : ℕ := 5*m+j.val+1
def residueEuler (j : Fin 4) (q : ℂ) : ℂ := ∏' m : ℕ, (1-q^(exponent j m))
def residueProduct (j : Fin 4) (q : ℂ) : ℂ := (residueEuler j q)⁻¹
def residueLog (j : Fin 4) (q : ℂ) : ℂ := -∑' m : ℕ, log (1-q^(exponent j m))
def product (b : Fin 4 → ℕ) (q : ℂ) : ℂ := ∏ j : Fin 4, (residueProduct j q)^(b j)
def productLog (b : Fin 4 → ℕ) (q : ℂ) : ℂ := ∑ j : Fin 4, (b j:ℂ)*residueLog j q

theorem exponent_pos (j : Fin 4) (m : ℕ) : 0 < exponent j m := by unfold exponent; omega

theorem powers_summable (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => ‖-q^(exponent j m)‖) := by
  have hi : Function.Injective (exponent j) := by intro a b he; unfold exponent at he; omega
  have hs := (summable_geometric_of_lt_one (norm_nonneg q) hq).comp_injective hi
  simpa only [norm_neg, norm_pow, Function.comp_def] using hs

theorem factors_multipliable (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun m : ℕ => 1-q^(exponent j m)) := by
  simpa only [← sub_eq_add_neg] using multipliable_one_add_of_summable (powers_summable j q hq)

theorem factor_ne_zero (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) (m : ℕ) :
    1-q^(exponent j m) ≠ 0 := EndpointEulerTail.factor_ne_zero q hq _ (exponent_pos j m)

theorem log_summable (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun m : ℕ => log (1-q^(exponent j m))) := by
  have hs := Complex.summable_log_one_add_of_summable (powers_summable j q hq).of_norm
  simpa only [← sub_eq_add_neg] using hs

theorem exp_residueLog (j : Fin 4) (q : ℂ) (hq : ‖q‖ < 1) :
    exp (residueLog j q)=residueProduct j q := by
  rw [residueLog, exp_neg, Complex.cexp_tsum_eq_tprod (factor_ne_zero j q hq) (log_summable j q hq)]
  rfl

theorem exp_productLog (b : Fin 4 → ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    exp (productLog b q)=product b q := by
  rw [productLog, Complex.exp_sum]
  unfold product
  apply Finset.prod_congr rfl
  intro j _
  rw [exp_nat_mul, exp_residueLog j q hq]

theorem product_ne_zero (b : Fin 4 → ℕ) (q : ℂ) (hq : ‖q‖ < 1) : product b q ≠ 0 := by
  rw [← exp_productLog b q hq]
  exact exp_ne_zero _

theorem product_norm (b : Fin 4 → ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖product b q‖=Real.exp (productLog b q).re := by
  rw [← exp_productLog b q hq, Complex.norm_exp]

end
end Borwein.PeriodicEulerProduct
