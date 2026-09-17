import Borwein.EndpointEtaBounds
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false

namespace Borwein.EndpointEulerTail
noncomputable section
open Complex EndpointEta Filter
open scoped Topology

def finiteEuler (N : ℕ) (q : ℂ) : ℂ := ∏ j ∈ Finset.range N, (1-q^(j+1))
def tailEuler (N : ℕ) (q : ℂ) : ℂ := ∏' j : ℕ, (1-q^(j+N+1))

theorem factor_ne_zero (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) (hk : 0 < k) : 1-q^k ≠ 0 := by
  have hn : ‖q^k‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (Nat.ne_of_gt hk)
  intro h
  have he : q^k = 1 := (sub_eq_zero.mp h).symm
  rw [he, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem finiteEuler_ne_zero (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) : finiteEuler N q ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun j _ => factor_ne_zero q hq (j+1) (by omega)

theorem tail_summable (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun j : ℕ => ‖-q^(j+N+1)‖) := by
  simpa only [norm_neg, norm_pow, Nat.add_assoc] using
    (summable_nat_add_iff (N+1)).mpr (summable_geometric_of_lt_one (norm_nonneg q) hq)

theorem tail_multipliable (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun j : ℕ => 1-q^(j+N+1)) := by
  simpa only [← sub_eq_add_neg] using multipliable_one_add_of_summable (tail_summable N q hq)

theorem tailEuler_ne_zero (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) : tailEuler N q ≠ 0 := by
  unfold tailEuler
  simp_rw [sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro j
    simpa only [← sub_eq_add_neg] using factor_ne_zero q hq (j+N+1) (by omega)
  · exact tail_summable N q hq

theorem euler_split (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    finiteEuler N q*tailEuler N q = euler q := by
  exact Multipliable.prod_mul_tprod_nat_mul' (f := fun j : ℕ => 1-q^(j+1)) (k := N)
    (tail_multipliable N q hq)

theorem tail_error (N : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖tailEuler N q-1‖ ≤ Real.exp (‖q‖^(N+1)/(1-‖q‖))-1 := by
  have hp := (tail_multipliable N q hq).hasProd
  have hs : HasSum (fun j : ℕ => ‖q‖^(j+N+1)) (‖q‖^(N+1)/(1-‖q‖)) := by
    simpa [pow_add, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasSum_geometric_of_lt_one (norm_nonneg q) hq).mul_left (‖q‖^(N+1))
  have hleft : Tendsto (fun s : Finset ℕ => ‖(∏ j ∈ s, (1-q^(j+N+1)))-1‖)
      atTop (𝓝 ‖tailEuler N q-1‖) := (hp.sub tendsto_const_nhds).norm
  have hright : Tendsto (fun s : Finset ℕ => Real.exp (∑ j ∈ s, ‖q‖^(j+N+1))-1)
      atTop (𝓝 (Real.exp (‖q‖^(N+1)/(1-‖q‖))-1)) :=
    (Real.continuous_exp.continuousAt.tendsto.comp hs).sub tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  exact Eventually.of_forall fun s => by
    simpa only [norm_neg, norm_pow, ← sub_eq_add_neg] using
      s.norm_prod_one_add_sub_one_le (fun j : ℕ => -q^(j+N+1))

end
end Borwein.EndpointEulerTail
