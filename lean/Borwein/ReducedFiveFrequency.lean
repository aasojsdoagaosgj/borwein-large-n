import Borwein.ResidueGeometricBound

set_option autoImplicit false

namespace Borwein.ReducedFiveFrequency
noncomputable section

theorem scaled_den (q : ℚ) (B : ℕ) (hb : q.den = 5*B) : ((5:ℚ)*q).den = B := by
  have hcop : q.num.natAbs.Coprime B := q.reduced.of_dvd_right (by rw [hb]; exact Nat.dvd_mul_left B 5)
  rw [Rat.mul_den,Int.natAbs_mul]
  norm_num
  rw [hb,Nat.gcd_mul_left,hcop.gcd_eq_one]
  simp

theorem residue_scaled (q : ℚ) (B k : ℕ) (hb : q.den = 5*B) :
    DirichletCover.residue q (5*k) = 5*DirichletCover.residue ((5:ℚ)*q) k := by
  unfold DirichletCover.residue
  rw [scaled_den q B hb,hb]
  push_cast
  rw [show (5:ℝ)*k*(q:ℝ) = (k:ℝ)*(5*q) by ring]
  ring

theorem resonance (q : ℚ) (B k : ℕ) (hb : q.den = 5*B) :
    q.den ∣ 5*k ↔ ((5:ℚ)*q).den ∣ k := by
  rw [scaled_den q B hb,hb]
  exact mul_dvd_mul_iff_left (by norm_num : (5:ℕ) ≠ 0)

end
end Borwein.ReducedFiveFrequency
