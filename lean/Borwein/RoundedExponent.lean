import Borwein.RoundedExponentData

namespace Borwein.RoundedExponent
noncomputable section
open Borwein.ExpCertificate

theorem finite_recurrence (lo hi : ℕ → ℝ) (N : ℕ)
    (hlo0 : lo 0 ≤ etaLo) (hhi0 : etaHi ≤ hi 0)
    (hlostep : ∀ i < N, lo (i+1) ≤ lo i*stepLo)
    (hhistep : ∀ i < N, hi i*stepHi ≤ hi (i+1)) (i : ℕ) (hiN : i ≤ N) :
    lo i ≤ Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ∧
      Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ≤ hi i := by
  have hs : 0 ≤ stepLo := by norm_num [stepLo, scale]
  have he : ∀ k, k ≤ N → lo k ≤ Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^k ∧
      Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^k ≤ hi k := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using And.intro (le_trans hlo0 exp_eta_bounds.1) (le_trans exp_eta_bounds.2 hhi0)
    | succ k ih =>
      intro hk
      have ih' := ih (Nat.le_of_succ_le hk)
      have hp : 0 ≤ Real.exp (-(113/40000:ℝ))*Real.exp (-(11/800:ℝ))^k := by positivity
      constructor
      · have h := mul_le_mul ih'.1 exp_step_bounds.1 hs hp
        have h' := le_trans (hlostep k hk) h
        simpa only [pow_succ, mul_assoc] using h'
      · have hipos := le_trans hp ih'.2
        have h := mul_le_mul ih'.2 exp_step_bounds.2 (Real.exp_pos _).le hipos
        have h' := le_trans h (hhistep k hk)
        simpa only [pow_succ, mul_assoc] using h'
  rw [cell_exp_factorization]
  exact he i hiN

def lower (i : ℕ) : ℝ := (RoundedExponentData.lo[i]!:ℝ)/scale
def upper (i : ℕ) : ℝ := (RoundedExponentData.hi[i]!:ℝ)/scale

theorem starts : lower 0 ≤ etaLo ∧ etaHi ≤ upper 0 := by
  have h := RoundedExponentData.starts
  simp only [lower, upper, h.1, h.2, etaLo, etaHi]
  constructor <;> rfl

theorem scaled_mul_lower (a b k D : ℕ) (hD : 0 < D) (h : b*D ≤ a*k) :
    (b:ℝ)/D ≤ ((a:ℝ)/D)*((k:ℝ)/D) := by
  have hp : 0 < (D:ℝ) := by exact_mod_cast hD
  rw [div_mul_div_comm, div_le_div_iff₀ hp (mul_pos hp hp)]
  have hh : (b:ℝ)*D ≤ (a:ℝ)*k := by exact_mod_cast h
  nlinarith

theorem scaled_mul_upper (a b k D : ℕ) (hD : 0 < D) (h : a*k ≤ b*D) :
    ((a:ℝ)/D)*((k:ℝ)/D) ≤ (b:ℝ)/D := by
  have hp : 0 < (D:ℝ) := by exact_mod_cast hD
  rw [div_mul_div_comm, div_le_div_iff₀ (mul_pos hp hp) hp]
  have hh : (a:ℝ)*k ≤ (b:ℝ)*D := by exact_mod_cast h
  nlinarith

theorem steps (i : ℕ) (hi : i < 400) :
    lower (i+1) ≤ lower i*stepLo ∧ upper i*stepHi ≤ upper (i+1) := by
  have h := RoundedExponentData.steps ⟨i,hi⟩
  constructor
  · have hs := scaled_mul_lower _ _ _ _ (show 0 < RoundedExponentData.D by decide) h.1
    simpa only [lower, stepLo, scale, RoundedExponentData.D, Nat.cast_ofNat] using hs
  · have hs := scaled_mul_upper _ _ _ _ (show 0 < RoundedExponentData.D by decide) h.2
    simpa only [upper, stepHi, scale, RoundedExponentData.D, Nat.cast_ofNat] using hs

theorem all_401_bounds (i : ℕ) (hi : i ≤ 400) :
    lower i ≤ Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ∧
      Real.exp (-((113/40000:ℝ)+(11/2:ℝ)*(i:ℝ)/400)) ≤ upper i :=
  finite_recurrence lower upper 400 starts.1 starts.2 (fun k hk => (steps k hk).1)
    (fun k hk => (steps k hk).2) i hi

end
end Borwein.RoundedExponent
