import Borwein.CiglerWeights

set_option autoImplicit false

namespace Borwein.WatsonWeights
noncomputable section
open Complex

def weight (q w : ℂ) (k : ℤ) : ℂ := (-1:ℂ)^k*q^(pentagonal (-k):ℤ)*w^(3*k)

theorem exponent_sub_one (k : ℤ) :
    (pentagonal (-(k-1)):ℤ)=(pentagonal (-k):ℤ)+(1-3*k) := by
  nlinarith [two_mul_natCast_pentagonal (-(k-1)), two_mul_natCast_pentagonal (-k)]

theorem weight_sub_one (q w : ℂ) (hq : q ≠ 0) (hw : w ≠ 0) (k : ℤ) :
    weight q w (k-1)= -(q/(w^3*(q^k)^3))*weight q w k := by
  have hs : (-1:ℂ)^(k-1) = -(-1:ℂ)^k := by
    rw [zpow_sub₀ (by norm_num), zpow_one]
    ring
  have hp : q^(3*k)=(q^k)^3 := by
    rw [show (3:ℤ)*k=k*3 by ring, zpow_mul, zpow_ofNat]
  unfold weight
  rw [hs, exponent_sub_one, zpow_add₀ hq, zpow_sub₀ hq, zpow_one, hp,
    show (3:ℤ)*(k-1)=3*k-3 by ring, zpow_sub₀ hw, zpow_ofNat]
  field_simp
  <;> ring

theorem weight_zero (q w : ℂ) : weight q w 0=1 := by
  simp [weight]

end
end Borwein.WatsonWeights
