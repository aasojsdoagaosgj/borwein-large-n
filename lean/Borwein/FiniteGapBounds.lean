import Borwein.ExpCertificate

namespace Borwein.FiniteGapBounds
noncomputable section
open scoped BigOperators
open Borwein.SincBounds Borwein.ResonantCertificate Borwein.ExpCertificate
open Borwein.SmoothedCertificate

theorem profile_nonneg (a : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ 2) : 0 ≤ profile a := by
  have hs : a^2 ≤ 4 := by nlinarith
  have h := mul_nonneg (sq_nonneg a) (show 0 ≤ 20-a^2 by linarith)
  unfold profile
  nlinarith

def lowerCertificate (lo hi : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ) (c : ℝ) :=
  ∑ d : Fin 4, ∑ i ∈ Finset.range n,
    (lo d i-hi d (i+1))*b (i+1)*profile (min 2 (((d:ℝ)+1)*c*b (i+1)))

theorem lowerCertificate_le (lo hi g : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ) (c : ℝ)
    (hc : 0 ≤ c) (hb : ∀ i < n, 0 ≤ b (i+1))
    (hlo : ∀ d i, i < n → lo d i ≤ g d i)
    (hhi : ∀ d i, i ≤ n → g d i ≤ hi d i) :
    lowerCertificate lo hi b n c ≤ certificate g b n c := by
  apply Finset.sum_le_sum
  intro d _
  apply Finset.sum_le_sum
  intro i hin
  have hin' := Finset.mem_range.mp hin
  apply mul_le_mul_of_nonneg_right
  · apply mul_le_mul_of_nonneg_right _ (hb i hin')
    exact sub_le_sub (hlo d i hin') (hhi d (i+1) hin')
  · apply profile_nonneg
    · apply le_min (by norm_num)
      exact mul_nonneg (mul_nonneg (by positivity) hc) (hb i hin')
    · exact min_le_left _ _

def exactLo (d : Fin 4) (i : ℕ) :=
  if i < 400 then min ((4-(d:ℝ))/25) (weightLo d (i+1)) else 0
def exactHi (d : Fin 4) (i : ℕ) :=
  if i < 400 then min ((4-(d:ℝ))/25) (weightHi d (i+1)) else 0

theorem exact_height_bounds (d : Fin 4) (i : ℕ) :
    exactLo d i ≤ shiftedHeights (uniformGrid 400) 400 (113/40000) (11/2) d i ∧
    shiftedHeights (uniformGrid 400) 400 (113/40000) (11/2) d i ≤ exactHi d i := by
  by_cases hi : i < 400
  · simp only [exactLo, exactHi, shiftedHeights, if_pos hi, uniformGrid]
    simpa only [mul_div_assoc, Nat.cast_ofNat] using all_cell_envelope_bounds d (i+1)
  · simp [exactLo, exactHi, shiftedHeights, hi]

def exactLowerGap :=
  lowerCertificate exactLo exactHi (uniformGrid 400) 400 (6/5)

theorem exactLowerGap_le :
    exactLowerGap ≤ uniformGap (113/40000) (11/2) (6/5) 400 := by
  apply lowerCertificate_le _ _ _ _ _ _ (by norm_num)
  · intro i _
    unfold uniformGrid
    positivity
  · exact fun d i _ => (exact_height_bounds d i).1
  · exact fun d i _ => (exact_height_bounds d i).2

theorem gap_of_rational_lower (q : ℝ) (hq : q ≤ exactLowerGap)
    (τ t : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2) (ht : 6/5 ≤ |t|) :
    Borwein.SmoothedPhase.smoothedModulus (113/40000) τ t ≤
      Borwein.PhaseIntegral.radialR τ-q := by
  have h := current_parameters_upper τ t hτ hT ht
  have hl := le_trans hq exactLowerGap_le
  linarith


theorem rounded_exp_recurrence (lo hi : ℕ → ℝ)
    (hlo0 : lo 0 ≤ etaLo) (hhi0 : etaHi ≤ hi 0)
    (hlostep : ∀ i, lo (i+1) ≤ lo i*stepLo)
    (hhistep : ∀ i, hi i*stepHi ≤ hi (i+1)) (i : ℕ) :
    lo i ≤ Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ∧
      Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ≤ hi i := by
  have hs : 0 ≤ stepLo := by norm_num [stepLo, scale]
  have he : ∀ i, lo i ≤ Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^i ∧
      Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^i ≤ hi i := by
    intro k
    induction k with
    | zero =>
      simpa using And.intro (le_trans hlo0 exp_eta_bounds.1) (le_trans exp_eta_bounds.2 hhi0)
    | succ k ih =>
      have hp : 0 ≤ Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^k := by positivity
      constructor
      · have h := mul_le_mul ih.1 exp_step_bounds.1 hs hp
        have h' := le_trans (hlostep k) h
        simpa only [pow_succ, mul_assoc] using h'
      · have hipos := le_trans hp ih.2
        have h := mul_le_mul ih.2 exp_step_bounds.2 (Real.exp_pos _).le hipos
        have h' := le_trans h (hhistep k)
        simpa only [pow_succ, mul_assoc] using h'
  rw [cell_exp_factorization]
  exact he i

end
end Borwein.FiniteGapBounds
