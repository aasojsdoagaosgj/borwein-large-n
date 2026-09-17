import Borwein.ScaledPeano

namespace Borwein.EulerMaclaurin
noncomputable section
open scoped BigOperators
open MeasureTheory Set PeanoQuadrature

def node (n k : ℕ) : ℝ := (k:ℝ)/n

theorem node_succ (n k : ℕ) : node n (k+1) = node n k+(n:ℝ)⁻¹ := by
  simp [node,Nat.cast_add,add_div,one_div]

theorem node_mem (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k ≤ n) : node n k ∈ Icc (0:ℝ) 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Nat.cast_nonneg k) hn'.le
  · exact (div_le_one hn').mpr (by exact_mod_cast hk)

theorem cell_subset (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n) :
    uIcc (node n k) (node n (k+1)) ⊆ Icc (0:ℝ) 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hm : node n k ≤ node n (k+1) := by
    rw [node_succ]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hn'.le)
  rw [uIcc_of_le hm]
  exact Icc_subset_Icc (node_mem n hn k hk.le).1 (node_mem n hn (k+1) hk).2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def residual (n : ℕ) (α : ℝ) (f0 f1 : ℝ → F) (k : ℕ) : F :=
  f0 (((k:ℝ)+α)/n)-(n:ℝ) • (∫ u in node n k..node n (k+1), f0 u)-
    B1 α • (f0 (node n (k+1))-f0 (node n k))-
    (B2 α/(2*n)) • (f1 (node n (k+1))-f1 (node n k))

theorem residual_bound (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (f0 f1 f2 f3 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 u) u)
    (hf3 : ContinuousOn f3 (Icc (0:ℝ) 1)) (k : ℕ) (hk : k < n) :
    ‖residual n α f0 f1 k‖ ≤ (n:ℝ)⁻¹^2 * (∫ u in node n k..node n (k+1), ‖f3 u‖) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hs : Icc (node n k) (node n k+(n:ℝ)⁻¹) ⊆ Icc (0:ℝ) 1 := by
    rw [← node_succ]
    apply (Icc_subset_uIcc).trans (cell_subset n hn k hk)
  have h := interval_error (node n k) (n:ℝ)⁻¹ α (inv_pos.mpr hn') ha0 ha1 f0 f1 f2 f3
    (fun u hu => hf0 u (hs hu)) (fun u hu => hf1 u (hs hu)) (fun u hu => hf2 u (hs hu)) (hf3.mono hs)
  have hx : node n k+(n:ℝ)⁻¹*α = ((k:ℝ)+α)/n := by unfold node; field_simp
  have hb : (n:ℝ)⁻¹*B2 α/2 = B2 α/(2*n) := by field_simp
  simpa only [← node_succ,inv_inv,hx,hb,residual] using h

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem differences_sum (u : ℕ → F) (n : ℕ) :
    (∑ k ∈ Finset.range n, (u (k+1)-u k)) = u n-u 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; abel

omit [CompleteSpace F] in
theorem integral_cells (n : ℕ) (hn : 0 < n) (f : ℝ → F) (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    (∑ k ∈ Finset.range n, ∫ u in node n k..node n (k+1), f u) = ∫ u in (0:ℝ)..1, f u := by
  have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (fun k hk => (hf.mono (cell_subset n hn k hk)).intervalIntegrable)
  simpa [node,ne_of_gt hn] using h

theorem residual_sum (n : ℕ) (hn : 0 < n) (α : ℝ) (f0 f1 : ℝ → F)
    (hf0 : ContinuousOn f0 (Icc (0:ℝ) 1)) :
    (∑ k ∈ Finset.range n, residual n α f0 f1 k) =
      (∑ k ∈ Finset.range n, f0 (((k:ℝ)+α)/n))-(n:ℝ) • (∫ u in (0:ℝ)..1, f0 u)-
      B1 α • (f0 1-f0 0)-(B2 α/(2*n)) • (f1 1-f1 0) := by
  have ht0 := differences_sum (fun k => f0 (node n k)) n
  have ht1 := differences_sum (fun k => f1 (node n k)) n
  simp only [Finset.sum_sub_distrib] at ht0 ht1
  simp only [residual,Finset.sum_sub_distrib,← Finset.smul_sum]
  rw [integral_cells n hn f0 hf0,ht0,ht1]
  simp [node,ne_of_gt hn]

theorem error_bound (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (f0 f1 f2 f3 : ℝ → F)
    (hf0 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 u) u)
    (hf1 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 u) u)
    (hf2 : ∀ u ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 u) u)
    (hf3 : ContinuousOn f3 (Icc (0:ℝ) 1)) :
    ‖(∑ k ∈ Finset.range n, f0 (((k:ℝ)+α)/n))-(n:ℝ) • (∫ u in (0:ℝ)..1, f0 u)-
      B1 α • (f0 1-f0 0)-(B2 α/(2*n)) • (f1 1-f1 0)‖ ≤
      (n:ℝ)⁻¹^2 * (∫ u in (0:ℝ)..1, ‖f3 u‖) := by
  have hc : ContinuousOn f0 (Icc (0:ℝ) 1) := fun u hu => (hf0 u hu).continuousAt.continuousWithinAt
  rw [← residual_sum n hn α f0 f1 hc]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖residual n α f0 f1 k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (n:ℝ)⁻¹^2 * (∫ u in node n k..node n (k+1), ‖f3 u‖) := by
      apply Finset.sum_le_sum
      intro k hk
      exact residual_bound n hn α ha0 ha1 f0 f1 f2 f3 hf0 hf1 hf2 hf3 k (Finset.mem_range.mp hk)
    _ = _ := by rw [← Finset.mul_sum,integral_cells n hn (fun u => ‖f3 u‖) hf3.norm]

end
end Borwein.EulerMaclaurin
