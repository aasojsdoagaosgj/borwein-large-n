import Borwein.LogFactorEulerMaclaurin

namespace Borwein.LogFactorDerivatives
noncomputable section
open scoped BigOperators
open MeasureTheory Set

def mainTerm (c z : ℂ) (n : ℕ) (α : ℝ) : ℂ :=
  (n:ℝ) • (∫ x in (0:ℝ)..1, f0 c z x)+PeanoQuadrature.B1 α • (f0 c z 1-f0 c z 0)+
    (PeanoQuadrature.B2 α/(2*n)) • (f1 c z 1-f1 c z 0)

def remainder (c z : ℂ) (n : ℕ) (α : ℝ) : ℂ :=
  (∑ k ∈ Finset.range n, f0 c z (((k:ℝ)+α)/n))-mainTerm c z n α

theorem sample_mem (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (k : ℕ) (hk : k < n) : ((k:ℝ)+α)/n ∈ Icc (0:ℝ) 1 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  constructor
  · positivity
  · apply (div_le_one hn').mpr
    have hh : (k:ℝ)+1 ≤ n := by exact_mod_cast hk
    linarith

theorem remainder_bound (c z : ℂ) (hc : ‖c‖ ≤ 1) (hz : 0 ≤ z.re) (d : ℝ) (hd : 0 < d)
    (hgap : ∀ x ∈ Icc (0:ℝ) 1, d ≤ ‖kernel c z x‖)
    (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) :
    ‖remainder c z n α‖ ≤ (n:ℝ)⁻¹^2 * (2*‖z‖^3/d^3) := by
  have h := log_error_bound c z hc hz d hd hgap n hn α ha0 ha1
  simpa only [remainder,mainTerm,sub_add_eq_sub_sub] using h

theorem product_expansion (c z : ℂ) (n : ℕ) (hn : 0 < n) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (hk : ∀ x ∈ Icc (0:ℝ) 1, kernel c z x ≠ 0) :
    (∏ k ∈ Finset.range n, kernel c z (((k:ℝ)+α)/n)) =
      Complex.exp (mainTerm c z n α+remainder c z n α) := by
  rw [remainder,add_sub_cancel,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro k hkr
  exact (Complex.exp_log (hk _ (sample_mem n hn α ha0 ha1 k (Finset.mem_range.mp hkr)))).symm

def shift (j : Fin 4) : ℝ := ((j.val:ℝ)+1)/5

theorem shift_mem (j : Fin 4) : shift j ∈ Icc (0:ℝ) 1 := by
  have hj : (j.val:ℝ) < 4 := by exact_mod_cast j.isLt
  unfold shift
  constructor
  · positivity
  · linarith

def fourRemainder (c : Fin 4 → ℂ) (z : ℂ) (n : ℕ) : ℂ := ∑ j : Fin 4, remainder (c j) z n (shift j)
def fourMain (c : Fin 4 → ℂ) (z : ℂ) (n : ℕ) : ℂ := ∑ j : Fin 4, mainTerm (c j) z n (shift j)

theorem four_remainder_bound (c : Fin 4 → ℂ) (z : ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) (hz : 0 ≤ z.re)
    (d : ℝ) (hd : 0 < d) (hgap : ∀ j x, x ∈ Icc (0:ℝ) 1 → d ≤ ‖kernel (c j) z x‖)
    (n : ℕ) (hn : 0 < n) :
    ‖fourRemainder c z n‖ ≤ (n:ℝ)⁻¹^2*(8*‖z‖^3/d^3) := by
  have h : ‖fourRemainder c z n‖ ≤ ∑ _j : Fin 4, (n:ℝ)⁻¹^2*(2*‖z‖^3/d^3) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    exact remainder_bound (c j) z (hc j) hz d hd (hgap j) n hn (shift j) (shift_mem j).1 (shift_mem j).2
  norm_num at h
  convert h using 1 <;> ring

theorem four_product_expansion (c : Fin 4 → ℂ) (z : ℂ) (n : ℕ) (hn : 0 < n)
    (hk : ∀ j x, x ∈ Icc (0:ℝ) 1 → kernel (c j) z x ≠ 0) :
    (∏ j : Fin 4, ∏ k ∈ Finset.range n, kernel (c j) z (((k:ℝ)+shift j)/n)) =
      Complex.exp (fourMain c z n+fourRemainder c z n) := by
  simp_rw [product_expansion _ _ n hn _ (shift_mem _).1 (shift_mem _).2 (hk _)]
  rw [← Complex.exp_sum]
  congr 1
  simp [fourMain,fourRemainder,Finset.sum_add_distrib]

theorem four_remainder_3400 (c : Fin 4 → ℂ) (z : ℂ) (hc : ∀ j, ‖c j‖ ≤ 1) (hz : 0 ≤ z.re)
    (hzmax : ‖z‖ ≤ 28/5)
    (hgap : ∀ j x, x ∈ Icc (0:ℝ) 1 → (3/4:ℝ) ≤ ‖kernel (c j) z x‖)
    (n : ℕ) (hn : 0 < n) : ‖fourRemainder c z n‖ ≤ 3400/(n:ℝ)^2 := by
  have h := four_remainder_bound c z hc hz (3/4) (by norm_num) hgap n hn
  have hp := pow_le_pow_left₀ (norm_nonneg z) hzmax 3
  have hb : 8*‖z‖^3/(3/4:ℝ)^3 ≤ 3400 := by norm_num at hp ⊢; linarith
  have hh := h.trans (mul_le_mul_of_nonneg_left hb (sq_nonneg (n:ℝ)⁻¹))
  simpa only [inv_pow,div_eq_mul_inv,mul_comm] using hh

end
end Borwein.LogFactorDerivatives
