import Borwein.EndpointSaddleIdentification
import Borwein.EndpointWeakIntegralZero

set_option autoImplicit false

namespace Borwein.EndpointScalarCorrection
noncomputable section

def term (x : ℝ) (p k : ℕ) : ℝ := x^k/(k:ℝ)^p
def value (x : ℝ) (p : ℕ) : ℝ := ∑' k : ℕ, term x p k
def sparse (x : ℝ) (p k : ℕ) : ℝ := if 5 ∣ k then term x p k else 0
def correction (x : ℝ) (p k : ℕ) : ℝ := 5*sparse x p k-term x p k

theorem term_nonneg (x : ℝ) (p k : ℕ) (hx : 0 ≤ x) : 0 ≤ term x p k := by unfold term; positivity

theorem term_summable (x : ℝ) (p : ℕ) (hp : 0 < p) (hx : 0 ≤ x) (hX : x < 1) :
    Summable (term x p) := by
  apply Summable.of_nonneg_of_le (fun k => term_nonneg x p k hx) _
    (summable_geometric_of_lt_one hx hX)
  intro k
  by_cases hk : k=0
  · subst k
    simp [term, zero_pow (Nat.ne_of_gt hp)]
  · have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    exact div_le_self (pow_nonneg hx k) (one_le_pow₀ hk1)

theorem value_nonneg (x : ℝ) (p : ℕ) (hx : 0 ≤ x) : 0 ≤ value x p :=
  tsum_nonneg (fun k => term_nonneg x p k hx)

theorem fifth_value_le (x : ℝ) (p : ℕ) (hp : 0 < p) (hx : 0 ≤ x) (hX : x < 1) :
    value (x^5) p ≤ value x p := by
  have hx5 : x^5 ≤ x := by nlinarith [pow_le_one₀ hx hX.le (n := 4), pow_nonneg hx 4]
  have hX5 : x^5 < 1 := hx5.trans_lt hX
  apply (term_summable (x^5) p hp (pow_nonneg hx 5) hX5).tsum_le_tsum _ (term_summable x p hp hx hX)
  intro k
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg hx 5) hx5 k) (by positivity)

theorem sparse_hasSum (x : ℝ) (p : ℕ) (hp : 0 < p) (hx : 0 ≤ x) (hX : x < 1) :
    HasSum (sparse x p) (value (x^5) p/(5:ℝ)^p) := by
  have hX5 : x^5 < 1 := pow_lt_one₀ hx hX (by norm_num)
  have hg := ((term_summable (x^5) p hp (pow_nonneg hx 5) hX5).hasSum).div_const ((5:ℝ)^p)
  have hi : Function.Injective (fun k : ℕ => 5*k) := by intro a b he; dsimp at he; omega
  apply (hi.hasSum_iff (f := sparse x p) (by
    intro k hk
    have hnd : ¬5 ∣ k := by rintro ⟨l,hl⟩; exact hk ⟨l,hl.symm⟩
    simp only [sparse, if_neg hnd])).mp
  exact hg.congr_fun (fun k => by
    simp only [Function.comp_def, sparse, dvd_mul_right, if_true, term, ← pow_mul,
      Nat.cast_mul, Nat.cast_ofNat, mul_pow]
    ring)

theorem correction_hasSum (x : ℝ) (p : ℕ) (hp : 0 < p) (hx : 0 ≤ x) (hX : x < 1) :
    HasSum (correction x p) (5*(value (x^5) p/(5:ℝ)^p)-value x p) :=
  ((sparse_hasSum x p hp hx hX).mul_left 5).sub (term_summable x p hp hx hX).hasSum

theorem correction_sum_nonpos (x : ℝ) (p : ℕ) (hp : p=1 ∨ p=2) (hx : 0 ≤ x) (hX : x < 1) :
    5*(value (x^5) p/(5:ℝ)^p)-value x p ≤ 0 := by
  have hp0 : 0 < p := by omega
  have hu := fifth_value_le x p hp0 hx hX
  have hl := value_nonneg x p hx
  rcases hp with rfl|rfl <;> norm_num at hu hl ⊢ <;> linarith

end
end Borwein.EndpointScalarCorrection
