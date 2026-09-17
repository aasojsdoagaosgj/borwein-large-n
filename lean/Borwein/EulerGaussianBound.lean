import Borwein.EulerPentagonalLimit
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Borwein.EulerGaussianBound
noncomputable section
open Complex EulerPentagonalLimit MeasureTheory Set

theorem pentagonal_square (j : ℤ) : (j:ℝ)^2 ≤ (pentagonal j:ℝ) := by
  have hi := two_mul_natCast_pentagonal j
  have hp : j^2 ≤ (pentagonal j:ℤ) := by
    rcases le_or_gt j 0 with hj | hj
    · nlinarith [mul_nonneg (show 0 ≤ -j by omega) (show 0 ≤ 1-j by omega)]
    · have hj1 : 1 ≤ j := by omega
      nlinarith [mul_nonneg (show 0 ≤ j by omega) (show 0 ≤ j-1 by omega)]
  exact_mod_cast hp

theorem gaussian_antitone (v : ℝ) (hv : 0 ≤ v) :
    AntitoneOn (fun x : ℝ => Real.exp (-v*x^2)) (Ici 0) := by
  intro a ha b hb hab
  apply Real.exp_le_exp.mpr
  have he := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hab 2) hv
  linarith

theorem gaussian_integer_sum (v : ℝ) (hv : 0 < v) :
    Summable (fun j : ℤ => Real.exp (-v*(j:ℝ)^2)) ∧
      ∑' j : ℤ, Real.exp (-v*(j:ℝ)^2) ≤ 1+Real.sqrt (Real.pi/v) := by
  have ha := gaussian_antitone v hv.le
  have hi := (integrable_exp_neg_mul_sq hv).integrableOn (s := Ioi (0:ℝ))
  have hn := ha.summable_of_integrableOn_Ioi_zero hi (fun x _ => (Real.exp_pos _).le)
  have ht := ha.tsum_add_one_le_integral hi (fun x _ => (Real.exp_pos _).le)
  rw [integral_gaussian_Ioi] at ht
  have hn' : Summable (fun k : ℕ => Real.exp (-v*((k:ℝ)+1)^2)) := by
    simpa using (summable_nat_add_iff 1).mpr hn
  let f : ℤ → ℝ := fun j => Real.exp (-v*(j:ℝ)^2)
  have hg : Summable (fun k : ℕ => f (-(k+1))) := by
    simpa only [f, Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one, neg_sq] using hn'
  have hp : Summable (fun k : ℕ => f (k+1)) := by
    simpa only [f, Int.cast_add, Int.cast_natCast, Int.cast_one] using hn'
  refine ⟨Summable.of_add_one_of_neg_add_one
    (f := fun j : ℤ => Real.exp (-v*(j:ℝ)^2)) hp hg, ?_⟩
  change (∑' j : ℤ, f j) ≤ _
  rw [tsum_of_add_one_of_neg_add_one (f := f) hp hg]
  simp only [f, Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, neg_sq,
    Int.cast_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, Real.exp_zero]
  simp only [Nat.cast_add, Nat.cast_one] at ht
  linarith

theorem euler_gaussian (q : ℂ) (v : ℝ) (hv : 0 < v) (hq0 : q ≠ 0)
    (hq : ‖q‖ = Real.exp (-v)) :
    ‖EndpointEta.euler q‖ ≤ 1+Real.sqrt (Real.pi/v) := by
  have hq1 : ‖q‖ < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs := pentagonal_majorant_summable q hq1
  have hg := gaussian_integer_sum v hv
  rw [euler_pentagonal_nonzero q hq1 hq0]
  calc
    _ ≤ ∑' j : ℤ, ‖EulerPentagonalCenter.atom q j‖ := norm_tsum_le_tsum_norm (atom_summable q hq1).norm
    _ = ∑' j : ℤ, ‖q‖^(pentagonal j) := tsum_congr (fun j => atom_norm q j)
    _ ≤ ∑' j : ℤ, Real.exp (-v*(j:ℝ)^2) := by
      apply hs.tsum_le_tsum _ hg.1
      intro j
      rw [hq, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (pentagonal_square j) hv.le]
    _ ≤ _ := hg.2

theorem euler_small_radius (q : ℂ) (v : ℝ) (hv : 0 < v) (hV : v ≤ 13/10000)
    (hq0 : q ≠ 0) (hq : ‖q‖ = Real.exp (-v)) :
    ‖EndpointEta.euler q‖ ≤ 2/Real.sqrt v := by
  have hvp := Real.sqrt_pos.mpr hv
  have hvsq := Real.sq_sqrt hv.le
  have hpsq := Real.sq_sqrt Real.pi_pos.le
  have hvs : Real.sqrt v ≤ 1/10 := by nlinarith
  have hps : Real.sqrt Real.pi ≤ 19/10 := by nlinarith [Real.pi_lt_d2, Real.sqrt_nonneg Real.pi]
  apply (euler_gaussian q v hv hq0 hq).trans
  rw [Real.sqrt_div Real.pi_pos.le]
  apply (le_div_iff₀ hvp).mpr
  have he : (1+Real.sqrt Real.pi/Real.sqrt v)*Real.sqrt v =
      Real.sqrt v+Real.sqrt Real.pi := by field_simp
  rw [he]
  linarith

end
end Borwein.EulerGaussianBound
