import Borwein.EndpointSharpTail
import Borwein.Dilogarithm

set_option autoImplicit false

namespace Borwein.EndpointTailMain
noncomputable section
open Complex EndpointSharpTail EndpointTailKernel

def lambda (x : ℂ) : ℂ := Dilogarithm.dilog (x^5)/5-Dilogarithm.dilog x
def sparseTerm (x : ℂ) (k : ℕ) : ℂ := if 5 ∣ k then x^k/(k:ℂ)^2 else 0
def lambdaTerm (x w : ℂ) (k : ℕ) : ℂ := (5*sparseTerm x k-x^k/(k:ℂ)^2)/(5*w)
def phaseTerm (ξ x : ℂ) (k : ℕ) : ℂ :=
  if 5 ∣ k then 0 else x^k/(k:ℂ)*(ξ^k/(1-ξ^k)+1/2)
def phase (ξ x : ℂ) : ℂ := ∑' k : ℕ, phaseTerm ξ x k

theorem sparse_hasSum (x : ℂ) (hx : ‖x‖ ≤ 1) :
    HasSum (sparseTerm x) (Dilogarithm.dilog (x^5)/25) := by
  have hx5 : ‖x^5‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  have hg := (Dilogarithm.hasSum_dilog (x^5) hx5).div_const 25
  have hj : Function.Injective (fun k : ℕ => 5*k) := by intro a b he; dsimp at he; omega
  apply (hj.hasSum_iff (f := sparseTerm x) (by
    intro k hk
    have hnd : ¬5 ∣ k := by
      rintro ⟨l,hl⟩
      exact hk ⟨l,hl.symm⟩
    simp only [sparseTerm, if_neg hnd])).mp
  exact hg.congr_fun (fun k => by
    simp only [Function.comp_def, sparseTerm, dvd_mul_right, if_true, ← pow_mul, Nat.cast_mul, Nat.cast_ofNat]
    ring)

theorem lambda_hasSum (x w : ℂ) (hx : ‖x‖ ≤ 1) :
    HasSum (lambdaTerm x w) (lambda x/(5*w)) := by
  have hg := (((sparse_hasSum x hx).mul_left 5).sub (Dilogarithm.hasSum_dilog x hx)).div_const (5*w)
  have he : (5*(Dilogarithm.dilog (x^5)/25)-Dilogarithm.dilog x)/(5*w) = lambda x/(5*w) := by
    unfold lambda
    ring
  rw [he] at hg
  exact hg

theorem main_term_split (ξ x w : ℂ) (hξ : IsPrimitiveRoot ξ 5) (hw : w ≠ 0) (k : ℕ) :
    x^k/(k:ℂ)*principal (ξ^k) ((k:ℂ)*w) = lambdaTerm x w k+phaseTerm ξ x k := by
  by_cases hk : k=0
  · subst k
    simp [lambdaTerm, sparseTerm, phaseTerm]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast hk
  by_cases hd : 5 ∣ k
  · have he := (hξ.pow_eq_one_iff_dvd k).mpr hd
    simp only [principal, he, ite_true, lambdaTerm, sparseTerm, if_pos hd, phaseTerm]
    field_simp
    ring
  · have he : ξ^k ≠ 1 := fun hh => hd ((hξ.pow_eq_one_iff_dvd k).mp hh)
    simp only [principal, if_neg he, lambdaTerm, sparseTerm, if_neg hd, phaseTerm]
    field_simp
    ring

theorem lambda_shift_hasSum (x w : ℂ) (hx : ‖x‖ ≤ 1) :
    HasSum (fun l : ℕ => lambdaTerm x w (l+1)) (lambda x/(5*w)) := by
  have hg := (hasSum_nat_add_iff' 1).mpr (lambda_hasSum x w hx)
  simpa [lambdaTerm, sparseTerm] using hg

theorem phase_shift_summable (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    Summable (fun l : ℕ => phaseTerm ξ (x n w) (l+1)) := by
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  have hs := (mainTerm_summable n ξ w hξ.pow_eq_one hn hw hi).sub
    (lambda_shift_hasSum (x n w) w (x_norm_lt_one n w hn hw).le).summable
  apply hs.congr
  intro l
  have he := main_term_split ξ (x n w) w hξ hw0 (l+1)
  change mainTerm n ξ w l-_=_
  unfold mainTerm
  rw [he]
  ring

theorem phase_summable (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) : Summable (phaseTerm ξ (x n w)) := by
  exact (summable_nat_add_iff 1).mp (phase_shift_summable n ξ w hξ hn hw hi)

theorem phase_shift_hasSum (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    HasSum (fun l : ℕ => phaseTerm ξ (x n w) (l+1)) (phase ξ (x n w)) := by
  have hg := (hasSum_nat_add_iff' 1).mpr (phase_summable n ξ w hξ hn hw hi).hasSum
  simpa [phaseTerm, phase] using hg

theorem main_sum (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    (∑' l : ℕ, mainTerm n ξ w l) = lambda (x n w)/(5*w)+phase ξ (x n w) := by
  have hw0 : w ≠ 0 := by intro he; simp [he] at hw
  have hg := (lambda_shift_hasSum (x n w) w (x_norm_lt_one n w hn hw).le).add
    (phase_shift_hasSum n ξ w hξ hn hw hi)
  have he : (fun l : ℕ => lambdaTerm (x n w) w (l+1)+phaseTerm ξ (x n w) (l+1)) = mainTerm n ξ w := by
    funext l
    exact (main_term_split ξ (x n w) w hξ hw0 (l+1)).symm
  rw [he] at hg
  exact hg.tsum_eq

/-- Manuscript (5.8), retaining the small exponential factor in the tail error. -/
theorem tail_expansion (n : ℕ) (ξ w : ℂ) (hξ : IsPrimitiveRoot ξ 5)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    ‖EndpointTailLog.tailLog n (ξ*exp (-w))-
      (lambda (x n w)/(5*w)+phase ξ (x n w))‖ ≤ 5*‖w‖*‖x n w‖/(1-‖x n w‖) := by
  rw [tailLog_decomposition n ξ w hξ.pow_eq_one hn hw hi, main_sum n ξ w hξ hn hw hi]
  simpa only [add_sub_cancel_left] using sharp_error_bound n ξ w hξ.pow_eq_one hn hw hi

theorem actual_root_primitive (j : Fin 4) : IsPrimitiveRoot (FivePoleCircle.zeta^(j.val+1)) 5 := by
  apply FivePoleCircle.zeta_primitive.pow_of_coprime
  fin_cases j <;> norm_num

theorem four_root_expansion (n : ℕ) (j : Fin 4) (w : ℂ)
    (hn : 0 < n) (hw : 0 < w.re) (hi : |w.im| ≤ 3*w.re/4) :
    ‖EndpointTailLog.tailLog n (FivePoleCircle.zeta^(j.val+1)*exp (-w))-
      (lambda (x n w)/(5*w)+phase (FivePoleCircle.zeta^(j.val+1)) (x n w))‖ ≤
        5*‖w‖*‖x n w‖/(1-‖x n w‖) :=
  tail_expansion n _ w (actual_root_primitive j) hn hw hi

end
end Borwein.EndpointTailMain
