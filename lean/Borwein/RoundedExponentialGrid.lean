import Borwein.ExpCertificate

set_option autoImplicit false

namespace Borwein.RoundedExponentialGrid
noncomputable section

theorem recurrence (lo hi : ℕ → ℝ) (δ l u : ℝ) (N : ℕ)
    (hl0 : 0 ≤ l) (hl : l ≤ Real.exp (-δ)) (hu : Real.exp (-δ) ≤ u)
    (hstart : lo 0 ≤ 1 ∧ 1 ≤ hi 0)
    (hstep : ∀ i < N, lo (i+1) ≤ lo i*l ∧ hi i*u ≤ hi (i+1))
    (i : ℕ) (hiN : i ≤ N) :
    lo i ≤ Real.exp (-δ*(i:ℝ)) ∧ Real.exp (-δ*(i:ℝ)) ≤ hi i := by
  have hpow : ∀ k ≤ N, lo k ≤ Real.exp (-δ)^k ∧ Real.exp (-δ)^k ≤ hi k := by
    intro k
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
      intro hk
      have hprev := ih (Nat.le_of_succ_le hk)
      have hs := hstep k hk
      have hp : 0 ≤ Real.exp (-δ)^k := by positivity
      have hlo := (hs.1).trans (mul_le_mul hprev.1 hl hl0 hp)
      have hhi := (mul_le_mul hprev.2 hu (Real.exp_pos _).le (hp.trans hprev.2)).trans hs.2
      simpa only [pow_succ] using And.intro hlo hhi
  have he : Real.exp (-δ)^i = Real.exp (-δ*(i:ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [← he]
  exact hpow i hiN

theorem scaled_lower (a b k D : ℕ) (hD : 0 < D) (h : b*D ≤ a*k) :
    (b:ℝ)/D ≤ ((a:ℝ)/D)*((k:ℝ)/D) := by
  have hp : 0 < (D:ℝ) := by exact_mod_cast hD
  rw [div_mul_div_comm,div_le_div_iff₀ hp (mul_pos hp hp)]
  have hh : (b:ℝ)*D ≤ (a:ℝ)*k := by exact_mod_cast h
  nlinarith

theorem scaled_upper (a b k D : ℕ) (hD : 0 < D) (h : a*k ≤ b*D) :
    ((a:ℝ)/D)*((k:ℝ)/D) ≤ (b:ℝ)/D := by
  have hp : 0 < (D:ℝ) := by exact_mod_cast hD
  rw [div_mul_div_comm,div_le_div_iff₀ (mul_pos hp hp) hp]
  have hh : (a:ℝ)*k ≤ (b:ℝ)*D := by exact_mod_cast h
  nlinarith

theorem checked_recurrence (lo hi : ℕ → ℕ) (D l u N : ℕ) (δ : ℝ) (hD : 0 < D)
    (hexp : (l:ℝ)/D ≤ Real.exp (-δ) ∧ Real.exp (-δ) ≤ (u:ℝ)/D)
    (hstart : lo 0 ≤ D ∧ D ≤ hi 0)
    (hstep : ∀ i < N, lo (i+1)*D ≤ lo i*l ∧ hi i*u ≤ hi (i+1)*D)
    (i : ℕ) (hiN : i ≤ N) :
    (lo i:ℝ)/D ≤ Real.exp (-δ*(i:ℝ)) ∧ Real.exp (-δ*(i:ℝ)) ≤ (hi i:ℝ)/D := by
  have hp : 0 < (D:ℝ) := by exact_mod_cast hD
  apply recurrence (fun j => (lo j:ℝ)/D) (fun j => (hi j:ℝ)/D) δ ((l:ℝ)/D) ((u:ℝ)/D) N
    (by positivity) hexp.1 hexp.2
  · constructor
    · apply (div_le_one hp).mpr
      exact_mod_cast hstart.1
    · apply (one_le_div hp).mpr
      exact_mod_cast hstart.2
  · intro j hj
    exact ⟨scaled_lower _ _ _ _ hD (hstep j hj).1,scaled_upper _ _ _ _ hD (hstep j hj).2⟩
  · exact hiN

end
end Borwein.RoundedExponentialGrid
