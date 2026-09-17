import Borwein.SineCertificate

set_option autoImplicit false

namespace Borwein.PeriodicSineLower
noncomputable section
open SineCertificate

def radius (m : ℕ) : ℚ :=
  2*(4:ℚ)^23/(23:ℕ).factorial+2*m*(rationalPiHi-rationalPiLo)

def Checked (x lo : ℚ) (m : ℕ) : Prop :=
  |x-(m:ℚ)*(2*rationalPiLo)| ≤ 4 ∧
    lo ≤ rationalPolynomial (x-(m:ℚ)*(2*rationalPiLo))-radius m

instance (x lo : ℚ) (m : ℕ) : Decidable (Checked x lo m) := inferInstanceAs (Decidable
  (|x-(m:ℚ)*(2*rationalPiLo)| ≤ 4 ∧
    lo ≤ rationalPolynomial (x-(m:ℚ)*(2*rationalPiLo))-radius m))

theorem polynomial_error_four (x : ℝ) (hx : |x| ≤ 4) :
    |Real.sin x-polynomial x| ≤ 2*(4:ℝ)^23/(23:ℕ).factorial := by
  have h := sine_error x 23 (by norm_num; linarith)
  rw [taylor_23] at h
  apply h.trans
  unfold error
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 23
  norm_num [Nat.factorial] at hp ⊢
  nlinarith

theorem period_error (x : ℝ) (m : ℕ) :
    |(x-(m:ℝ)*(2*Real.pi))-(x-(m:ℝ)*(2*piLo))| ≤ 2*m*(piHi-piLo) := by
  have he : (x-(m:ℝ)*(2*Real.pi))-(x-(m:ℝ)*(2*piLo)) = -(2*m*(Real.pi-piLo)) := by ring
  rw [he,abs_neg,abs_of_nonneg (by positivity [pi_bounds.1])]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right pi_bounds.2 _) (by positivity)

theorem shifted_lower (x lo : ℝ) (m : ℕ)
    (hx : |x-(m:ℝ)*(2*piLo)| ≤ 4)
    (hl : lo ≤ polynomial (x-(m:ℝ)*(2*piLo))-
      (2*(4:ℝ)^23/(23:ℕ).factorial+2*m*(piHi-piLo))) : lo ≤ Real.sin x := by
  have ht := polynomial_error_four (x-(m:ℝ)*(2*piLo)) hx
  have hp := (Real.abs_sin_sub_sin_le (x-(m:ℝ)*(2*Real.pi)) (x-(m:ℝ)*(2*piLo))).trans (period_error x m)
  rw [Real.sin_sub_nat_mul_two_pi] at hp
  have h1 := (abs_le.mp ht).1
  have h2 := (abs_le.mp hp).1
  linarith

theorem checked_sound (x lo : ℚ) (m : ℕ) (h : Checked x lo m) : (lo:ℝ) ≤ Real.sin x := by
  apply shifted_lower x lo m
  · have hx : |((x-(m:ℚ)*(2*rationalPiLo):ℚ):ℝ)| ≤ (4:ℝ) := by exact_mod_cast h.1
    simpa [cast_pi_lo] using hx
  · have hl : (lo:ℝ) ≤ ((rationalPolynomial (x-(m:ℚ)*(2*rationalPiLo))-radius m:ℚ):ℝ) := by exact_mod_cast h.2
    simpa [radius,cast_polynomial,cast_pi_lo,cast_pi_hi] using hl

end
end Borwein.PeriodicSineLower
