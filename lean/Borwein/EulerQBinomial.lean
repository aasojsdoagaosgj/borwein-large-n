import Borwein.EndpointEulerTail
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Borwein.EulerQBinomial
noncomputable section
open Complex EndpointEulerTail

/-- Analytic Gaussian binomial coefficient, including zero outside its range. -/
def gaussian (q : ℂ) (n k : ℕ) : ℂ :=
  if k ≤ n then finiteEuler n q / (finiteEuler k q * finiteEuler (n-k) q) else 0

theorem pochhammer_zero (q : ℂ) : finiteEuler 0 q = 1 := by simp [finiteEuler]

theorem pochhammer_succ (q : ℂ) (n : ℕ) :
    finiteEuler (n+1) q = finiteEuler n q * (1-q^(n+1)) := by
  simp [finiteEuler, Finset.prod_range_succ]

theorem gaussian_outside (q : ℂ) (n k : ℕ) (h : n < k) : gaussian q n k=0 := by
  simp [gaussian, Nat.not_le_of_gt h]

theorem gaussian_zero (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) : gaussian q n 0=1 := by
  simp [gaussian, pochhammer_zero, finiteEuler_ne_zero n q hq]

theorem gaussian_diagonal (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) : gaussian q n n=1 := by
  simp [gaussian, pochhammer_zero, finiteEuler_ne_zero n q hq]

theorem gaussian_symmetry (q : ℂ) (n k : ℕ) (hk : k ≤ n) :
    gaussian q n (n-k)=gaussian q n k := by
  simp [gaussian, hk, Nat.sub_sub_self hk, mul_comm]

/-- Pascal recurrence with the power on the unshifted column. -/
theorem gaussian_succ (q : ℂ) (n k : ℕ) (hq : ‖q‖ < 1) :
    gaussian q (n+1) (k+1)=gaussian q n k+q^(k+1)*gaussian q n (k+1) := by
  by_cases hkn : k < n
  · have hk : k ≤ n := hkn.le
    have hk1 : k+1 ≤ n := hkn
    have he : n-k=(n-(k+1))+1 := by omega
    have hp : q^(k+1)*q^(n-(k+1)+1)=q^(n+1) := by rw [← pow_add]; congr 1; omega
    simp only [gaussian, if_pos (show k+1 ≤ n+1 by omega), if_pos hk, if_pos hk1,
      Nat.add_sub_add_right]
    rw [pochhammer_succ q n, pochhammer_succ q k,
      show finiteEuler (n-k) q=finiteEuler (n-(k+1)) q*(1-q^(n-(k+1)+1)) by
        rw [he, pochhammer_succ]]
    have h1 := finiteEuler_ne_zero k q hq
    have h2 := finiteEuler_ne_zero (n-(k+1)) q hq
    have h3 := factor_ne_zero q hq (k+1) (by omega)
    have h4 := factor_ne_zero q hq (n-(k+1)+1) (by omega)
    field_simp
    linear_combination (finiteEuler n q)*hp
  · by_cases he : k=n
    · subst k
      rw [gaussian_diagonal q (n+1) hq, gaussian_diagonal q n hq,
        gaussian_outside q n (n+1) (by omega)]
      ring
    · have hk : n < k := by omega
      rw [gaussian_outside q (n+1) (k+1) (by omega), gaussian_outside q n k hk,
        gaussian_outside q n (k+1) (by omega)]
      ring

/-- The equivalent recurrence used when the last factor of the finite product is appended. -/
theorem gaussian_succ_right (q : ℂ) (n k : ℕ) (hq : ‖q‖ < 1) (hk : k ≤ n) :
    gaussian q (n+1) (k+1)=gaussian q n (k+1)+q^(n-k)*gaussian q n k := by
  by_cases he : k=n
  · subst k
    rw [gaussian_diagonal q (n+1) hq, gaussian_outside q n (n+1) (by omega),
      gaussian_diagonal q n hq]
    simp
  · have hkn : k < n := by omega
    have hr := gaussian_succ q n (n-k-1) hq
    have he1 : n-k-1+1=n-k := by omega
    rw [he1] at hr
    rw [← gaussian_symmetry q (n+1) (k+1) (by omega)]
    simp only [Nat.add_sub_add_right]
    rw [hr]
    rw [show n-k-1=n-(k+1) by omega,
      gaussian_symmetry q n (k+1) (by omega), gaussian_symmetry q n k hk]

end
end Borwein.EulerQBinomial
