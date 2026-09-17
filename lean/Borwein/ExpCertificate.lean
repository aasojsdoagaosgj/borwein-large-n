import Borwein.SmoothedCertificate
import Mathlib.Analysis.Complex.Exponential

namespace Borwein.ExpCertificate
noncomputable section
open scoped BigOperators

def taylorSum (x : ℝ) (n : ℕ) := ∑ j ∈ Finset.range n, x^j/(j.factorial:ℝ)
def remainder (x : ℝ) (n : ℕ) := |x|^n*((n+1:ℕ):ℝ)/((n.factorial:ℝ)*(n:ℝ))

theorem exp_enclosure (x lo hi : ℝ) (n : ℕ) (hx : |x| ≤ 1) (hn : 0 < n)
    (hlo : lo ≤ taylorSum x n-remainder x n)
    (hhi : taylorSum x n+remainder x n ≤ hi) :
    lo ≤ Real.exp x ∧ Real.exp x ≤ hi := by
  have h := Real.exp_bound hx hn
  have he : |Real.exp x-taylorSum x n| ≤ remainder x n := by
    simpa [taylorSum, remainder, mul_div_assoc] using h
  have hab := abs_le.mp he
  constructor <;> linarith

def scale : ℝ := 100000000000000000000
def etaLo : ℝ := 99717898655760799613/scale
def etaHi : ℝ := 99717898655760799614/scale
def stepLo : ℝ := 98634409946704400002/scale
def stepHi : ℝ := 98634409946704400003/scale

theorem exp_eta_bounds :
    etaLo ≤ Real.exp (-(113/40000:ℝ)) ∧ Real.exp (-(113/40000:ℝ)) ≤ etaHi := by
  apply exp_enclosure _ _ _ 10 (by norm_num) (by norm_num)
  all_goals norm_num [taylorSum, remainder, etaLo, etaHi, scale, Finset.sum_range_succ, Nat.factorial]

theorem exp_step_bounds :
    stepLo ≤ Real.exp (-(11/800:ℝ)) ∧ Real.exp (-(11/800:ℝ)) ≤ stepHi := by
  apply exp_enclosure _ _ _ 10 (by norm_num) (by norm_num)
  all_goals norm_num [taylorSum, remainder, stepLo, stepHi, scale, Finset.sum_range_succ, Nat.factorial]

theorem cell_exp_factorization (i : ℕ) :
    Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) =
      Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^i := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  ring

theorem all_cell_exp_bounds (i : ℕ) :
    etaLo*stepLo^i ≤ Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ∧
      Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ≤ etaHi*stepHi^i := by
  rw [cell_exp_factorization]
  have hl0 : 0 ≤ etaLo := by norm_num [etaLo, scale]
  have hs0 : 0 ≤ stepLo := by norm_num [stepLo, scale]
  constructor
  · exact mul_le_mul exp_eta_bounds.1 (pow_le_pow_left₀ hs0 exp_step_bounds.1 i)
      (pow_nonneg hs0 i) (Real.exp_pos _).le
  · exact mul_le_mul exp_eta_bounds.2
      (pow_le_pow_left₀ (Real.exp_pos _).le exp_step_bounds.2 i)
      (pow_nonneg (Real.exp_pos _).le i) (le_trans (Real.exp_pos _).le exp_eta_bounds.2)


open Borwein.GroupedWeights

theorem numerator_nonneg (d : Fin 4) (y : ℝ) (hy : 0 ≤ y) : 0 ≤ numerator d y := by
  fin_cases d <;> norm_num [numerator] <;> positivity

theorem numerator_mono (d : Fin 4) (l u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) :
    numerator d l ≤ numerator d u := by
  fin_cases d <;> norm_num [numerator] <;> gcongr

theorem denominator_mono (l u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) :
    denominator l ≤ denominator u := by
  unfold denominator
  gcongr

theorem weight_enclosure (d : Fin 4) (l y u : ℝ) (hl : 0 ≤ l) (hly : l ≤ y) (hyu : y ≤ u) :
    numerator d l / denominator u^2 ≤ weight d y ∧
      weight d y ≤ numerator d u / denominator l^2 := by
  have hy := le_trans hl hly
  have hu := le_trans hy hyu
  constructor
  · exact div_le_div₀ (numerator_nonneg d y hy) (numerator_mono d l y hl hly)
      (pow_pos (denominator_pos y hy) 2)
      (pow_le_pow_left₀ (denominator_pos y hy).le (denominator_mono y u hy hyu) 2)
  · exact div_le_div₀ (numerator_nonneg d u hu) (numerator_mono d y u hy hyu)
      (pow_pos (denominator_pos l hl) 2)
      (pow_le_pow_left₀ (denominator_pos l hl).le (denominator_mono l y hl hly) 2)

def weightLo (d : Fin 4) (i : ℕ) : ℝ :=
  numerator d (etaLo*stepLo^i) / denominator (etaHi*stepHi^i)^2
def weightHi (d : Fin 4) (i : ℕ) : ℝ :=
  numerator d (etaHi*stepHi^i) / denominator (etaLo*stepLo^i)^2

theorem all_cell_weight_bounds (d : Fin 4) (i : ℕ) :
    weightLo d i ≤ radial d ((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400) ∧
      radial d ((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400) ≤ weightHi d i := by
  have he := all_cell_exp_bounds i
  exact weight_enclosure d _ _ _ (by
    have hη : 0 ≤ etaLo := by norm_num [etaLo, scale]
    have hs : 0 ≤ stepLo := by norm_num [stepLo, scale]
    positivity) he.1 he.2

theorem all_cell_envelope_bounds (d : Fin 4) (i : ℕ) :
    min ((4-(d:ℝ))/25) (weightLo d i) ≤
      envelope d ((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400) ∧
    envelope d ((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400) ≤
      min ((4-(d:ℝ))/25) (weightHi d i) := by
  unfold envelope
  rw [Borwein.SmoothedCertificate.radial_at_zero]
  exact ⟨min_le_min_left _ (all_cell_weight_bounds d i).1,
    min_le_min_left _ (all_cell_weight_bounds d i).2⟩

end
end Borwein.ExpCertificate


