import Borwein.EulerPentagonalLimit
import Borwein.CiglerAdjacent

set_option autoImplicit false

namespace Borwein.PentagonalMiddle
noncomputable section
open Complex EndpointEta EulerPentagonalCenter EulerPentagonalLimit

def filtered (q : ℂ) (j : ℤ) : ℂ := if pentagonal j % 5=1 then atom q j else 0

theorem residue_one_iff (j : ℤ) : pentagonal j % 5=1 ↔ j%5=1 := by
  have he := two_mul_natCast_pentagonal j
  have hm := congrArg (fun z : ℤ => z%5) he
  have hj : 0 ≤ j%5 ∧ j%5 < 5 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
  rcases hj with ⟨hj0,hj5⟩
  rw [Int.mul_emod 2 _, Int.mul_emod j _, Int.sub_emod, Int.mul_emod 3 j] at hm
  interval_cases h : j%5 <;> norm_num [h] at hm ⊢ <;> omega

theorem exponent_middle (j : ℤ) : pentagonal (5*j+1)=1+25*pentagonal (-j) := by
  have he : (pentagonal (5*j+1):ℤ)=1+25*(pentagonal (-j):ℤ) := by
    nlinarith [two_mul_natCast_pentagonal (5*j+1), two_mul_natCast_pentagonal (-j)]
  exact_mod_cast he

theorem atom_middle (q : ℂ) (j : ℤ) : atom q (5*j+1)= -q*atom (q^25) (-j) := by
  have hs : (-1:ℂ)^(5*j+1) = -(-1:ℂ)^j := by
    rw [zpow_add₀ (by norm_num), zpow_mul]
    norm_num
  simp only [atom, hs, exponent_middle, pow_add, pow_one, pow_mul, CiglerWeights.sign_neg]
  ring

theorem filtered_sum (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' j : ℤ, filtered q j)= -q*euler (q^25) := by
  have hi : Function.Injective (fun j : ℤ => 5*j+1) := by
    intro i j hij
    change 5*i+1=5*j+1 at hij
    omega
  have hs := (atom_summable q hq).comp_injective hi
  have hf : HasSum (filtered q) (∑' j : ℤ, atom q (5*j+1)) := by
    apply (hi.hasSum_iff (f := filtered q) (by
      intro j hj
      have hmod : j%5 ≠ 1 := by
        intro he
        exact hj ⟨j/5, by change 5*(j/5)+1=j; omega⟩
      simp only [filtered, residue_one_iff, if_neg hmod])).mp
    exact hs.hasSum.congr_fun (fun j => by
      simp only [Function.comp_def, filtered, residue_one_iff]
      rw [if_pos (by omega)])
  rw [hf.tsum_eq]
  simp_rw [atom_middle]
  rw [tsum_mul_left, CiglerAdjacent.neg_reindex (atom (q^25))]
  have hq25 : ‖q^25‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  rw [← euler_pentagonal_nonzero (q^25) hq25 (pow_ne_zero _ hq0)]

end
end Borwein.PentagonalMiddle
