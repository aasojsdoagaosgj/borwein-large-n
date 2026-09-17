import Borwein.WatsonWeights
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false

namespace Borwein.WatsonThetaExponent
noncomputable section
open Complex

def exponent (r t : ℕ) (k : ℤ) : ℤ :=
  5*(pentagonal (-k):ℤ)-3*(r:ℤ)*k+(t:ℤ)*(10*k+5-2*(r:ℤ))
def degree (r t : ℕ) (k : ℤ) : ℕ := (exponent r t k).toNat

theorem twice_exponent (r t : ℕ) (k : ℤ) :
    2*exponent r t k=15*k*k+(5-6*(r:ℤ)+20*(t:ℤ))*k+2*(t:ℤ)*(5-2*(r:ℤ)) := by
  unfold exponent
  nlinarith [two_mul_natCast_pentagonal (-k)]

theorem exponent_nonneg (r t : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2)
    (ht : t ≤ 1) (k : ℤ) : 0 ≤ exponent r t k := by
  have he := twice_exponent r t k
  have hk : k ≤ -2 ∨ k = -1 ∨ k = 0 ∨ 1 ≤ k := by omega
  interval_cases r <;> interval_cases t <;> norm_num at he <;>
    rcases hk with hk | hk | hk | hk
  all_goals first
    | (subst k; norm_num at he; omega)
    | nlinarith [mul_nonneg (show 0 ≤ -k by omega) (show 0 ≤ -k-2 by omega)]
    | nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ k-1 by omega)]

theorem degree_cast (r t : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2)
    (ht : t ≤ 1) (k : ℤ) : (degree r t k:ℤ)=exponent r t k :=
  Int.toNat_of_nonneg (exponent_nonneg r t hr0 hr ht k)

theorem degree_injective (r t : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ 2)
    (ht : t ≤ 1) : Function.Injective (degree r t) := by
  intro i j hij
  have he : exponent r t i=exponent r t j := by
    rw [← degree_cast r t hr0 hr ht i, ← degree_cast r t hr0 hr ht j, hij]
  have hf : (i-j)*(15*(i+j)+5-6*(r:ℤ)+20*(t:ℤ))=0 := by
    nlinarith [twice_exponent r t i, twice_exponent r t j]
  have hn : 15*(i+j)+5-6*(r:ℤ)+20*(t:ℤ) ≠ 0 := by
    interval_cases r <;> interval_cases t <;> norm_num <;> omega
  exact sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hn)

theorem majorant_summable (x : ℂ) (hx : ‖x‖ < 1) (r t : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ 2) (ht : t ≤ 1) :
    Summable (fun k : ℤ => ‖x‖^(degree r t k)) := by
  simpa only [Function.comp_def] using
    (summable_geometric_of_lt_one (norm_nonneg x) hx).comp_injective
      (degree_injective r t hr0 hr ht)

def term (x : ℂ) (r : ℕ) (k : ℤ) : ℂ :=
  (-1:ℂ)^k*(x^(degree r 0 k)-x^(degree r 1 k))

theorem term_bound (x : ℂ) (r : ℕ) (k : ℤ) :
    ‖term x r k‖ ≤ ‖x‖^(degree r 0 k)+‖x‖^(degree r 1 k) := by
  simpa [term] using norm_sub_le (x^(degree r 0 k)) (x^(degree r 1 k))

theorem term_summable (x : ℂ) (hx : ‖x‖ < 1) (r : ℕ)
    (hr0 : 1 ≤ r) (hr : r ≤ 2) : Summable (term x r) :=
  ((majorant_summable x hx r 0 hr0 hr (by omega)).add
    (majorant_summable x hx r 1 hr0 hr (by omega))).of_norm_bounded (term_bound x r)

end
end Borwein.WatsonThetaExponent
