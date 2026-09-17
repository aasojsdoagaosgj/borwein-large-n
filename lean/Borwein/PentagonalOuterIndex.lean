import Borwein.PentagonalMiddle
import Borwein.WatsonThetaExponent

set_option autoImplicit false

namespace Borwein.PentagonalOuterIndex
noncomputable section
open Complex EulerPentagonalCenter WatsonThetaExponent

theorem residue_zero_iff (j : ℤ) : pentagonal j % 5=0 ↔ j%5=0 ∨ j%5=2 := by
  have hm := congrArg (fun z : ℤ => z%5) (two_mul_natCast_pentagonal j)
  have hj0 := Int.emod_nonneg j (by norm_num : (5:ℤ) ≠ 0)
  have hj5 := Int.emod_lt_of_pos j (by norm_num : (0:ℤ) < 5)
  rw [Int.mul_emod 2 _, Int.mul_emod j _, Int.sub_emod, Int.mul_emod 3 j] at hm
  interval_cases h : j%5 <;> norm_num [h] at hm ⊢ <;> omega

theorem residue_two_iff (j : ℤ) : pentagonal j % 5=2 ↔ j%5=3 ∨ j%5=4 := by
  have hm := congrArg (fun z : ℤ => z%5) (two_mul_natCast_pentagonal j)
  have hj0 := Int.emod_nonneg j (by norm_num : (5:ℤ) ≠ 0)
  have hj5 := Int.emod_lt_of_pos j (by norm_num : (0:ℤ) < 5)
  rw [Int.mul_emod 2 _, Int.mul_emod j _, Int.sub_emod, Int.mul_emod 3 j] at hm
  interval_cases h : j%5 <;> norm_num [h] at hm ⊢ <;> omega

theorem exponent_zero_first (k : ℤ) : pentagonal (5*k)=5*degree 1 0 k := by
  have hd := degree_cast 1 0 (by omega) (by omega) (by omega) k
  have he := twice_exponent 1 0 k
  have hp := two_mul_natCast_pentagonal (5*k)
  have hh : (pentagonal (5*k):ℤ)=5*(degree 1 0 k:ℤ) := by norm_num at he; nlinarith
  exact_mod_cast hh

theorem exponent_zero_second (k : ℤ) : pentagonal (-5*k-3)=5*degree 1 1 k := by
  have hd := degree_cast 1 1 (by omega) (by omega) (by omega) k
  have he := twice_exponent 1 1 k
  have hp := two_mul_natCast_pentagonal (-5*k-3)
  have hh : (pentagonal (-5*k-3):ℤ)=5*(degree 1 1 k:ℤ) := by norm_num at he; nlinarith
  exact_mod_cast hh

theorem exponent_two_first (k : ℤ) : pentagonal (5*k-1)=2+5*degree 2 0 k := by
  have hd := degree_cast 2 0 (by omega) (by omega) (by omega) k
  have he := twice_exponent 2 0 k
  have hp := two_mul_natCast_pentagonal (5*k-1)
  have hh : (pentagonal (5*k-1):ℤ)=2+5*(degree 2 0 k:ℤ) := by norm_num at he; nlinarith
  exact_mod_cast hh

theorem exponent_two_second (k : ℤ) : pentagonal (-5*k-2)=2+5*degree 2 1 k := by
  have hd := degree_cast 2 1 (by omega) (by omega) (by omega) k
  have he := twice_exponent 2 1 k
  have hp := two_mul_natCast_pentagonal (-5*k-2)
  have hh : (pentagonal (-5*k-2):ℤ)=2+5*(degree 2 1 k:ℤ) := by norm_num at he; nlinarith
  exact_mod_cast hh

theorem atom_zero_pair (q : ℂ) (k : ℤ) :
    atom q (5*k)+atom q (-5*k-3)=term (q^5) 1 k := by
  have hs : (-1:ℂ)^(5*k)=(-1:ℂ)^k := by rw [zpow_mul]; norm_num
  have ht : (-1:ℂ)^(-5*k-3)= -(-1:ℂ)^k := by
    rw [zpow_sub₀ (by norm_num), show (-5:ℤ)*k= -(5*k) by ring,
      CiglerWeights.sign_neg, hs]
    norm_num
    ring
  simp only [atom, hs, ht, exponent_zero_first, exponent_zero_second, pow_mul, term]
  ring

theorem atom_two_pair (q : ℂ) (k : ℤ) :
    atom q (5*k-1)+atom q (-5*k-2)= -q^2*term (q^5) 2 k := by
  have hs : (-1:ℂ)^(5*k)=(-1:ℂ)^k := by rw [zpow_mul]; norm_num
  have h1 : (-1:ℂ)^(5*k-1)= -(-1:ℂ)^k := by
    rw [zpow_sub₀ (by norm_num), hs]
    norm_num
    ring
  have h2 : (-1:ℂ)^(-5*k-2)=(-1:ℂ)^k := by
    rw [zpow_sub₀ (by norm_num), show (-5:ℤ)*k= -(5*k) by ring,
      CiglerWeights.sign_neg, hs]
    norm_num
  simp only [atom, h1, h2, exponent_two_first, exponent_two_second, pow_add, pow_mul, term]
  ring

end
end Borwein.PentagonalOuterIndex
