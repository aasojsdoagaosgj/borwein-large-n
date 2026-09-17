import Borwein.PentagonalOuterIndex
import Borwein.WatsonQuintupleProduct

set_option autoImplicit false

namespace Borwein.PentagonalOuterSum
noncomputable section
open Complex EndpointEta EulerPentagonalCenter EulerPentagonalLimit PentagonalOuterIndex
  WatsonThetaExponent RogersProducts

def classTerm (q : ℂ) (c j : ℤ) : ℂ := if j%5=c%5 then atom q j else 0
def filtered (q : ℂ) (a : ℕ) (j : ℤ) : ℂ := if pentagonal j%5=a then atom q j else 0

theorem affine_injective (c : ℤ) : Function.Injective (fun k : ℤ => 5*k+c) := by
  intro i j hij
  change 5*i+c=5*j+c at hij
  omega

theorem class_summable (q : ℂ) (hq : ‖q‖ < 1) (c : ℤ) : Summable (classTerm q c) := by
  apply (atom_summable q hq).norm.of_norm_bounded
  intro j
  unfold classTerm
  split_ifs <;> simp

theorem class_sum (q : ℂ) (hq : ‖q‖ < 1) (c : ℤ) :
    (∑' j : ℤ, classTerm q c j)=∑' k : ℤ, atom q (5*k+c) := by
  have hi := affine_injective c
  have hs := (atom_summable q hq).comp_injective hi
  have hh : HasSum (classTerm q c) (∑' k : ℤ, atom q (5*k+c)) := by
    apply (hi.hasSum_iff (f := classTerm q c) (by
      intro j hj
      have hm : j%5 ≠ c%5 := by
        intro he
        exact hj ⟨(j-c)/5, by change 5*((j-c)/5)+c=j; omega⟩
      simp only [classTerm, if_neg hm])).mp
    exact hs.hasSum.congr_fun (fun k => by
      simp only [Function.comp_def, classTerm]
      rw [if_pos (by omega)])
  exact hh.tsum_eq

theorem reverse_sum (q : ℂ) (c : ℤ) :
    (∑' k : ℤ, atom q (5*k+c))=∑' k : ℤ, atom q (-5*k+c) := by
  have hh := CiglerAdjacent.neg_reindex (fun k : ℤ => atom q (5*k+c))
  simpa only [mul_neg, neg_mul] using hh.symm

theorem filtered_zero_sum (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' j : ℤ, filtered q 0 j)=∑' k : ℤ, term (q^5) 1 k := by
  have he (j : ℤ) : filtered q 0 j=classTerm q 0 j+classTerm q (-3) j := by
    simp only [filtered, classTerm, residue_zero_iff]
    change (if j%5=0 ∨ j%5=2 then atom q j else 0)=
      (if j%5=0 then atom q j else 0)+(if j%5=2 then atom q j else 0)
    by_cases h0 : j%5=0
    · have h2 : j%5 ≠ 2 := by omega
      simp [h0,h2]
    · by_cases h2 : j%5=2 <;> simp [h0,h2]
  simp_rw [he]
  rw [(class_summable q hq 0).tsum_add (class_summable q hq (-3)),
    class_sum q hq 0, class_sum q hq (-3), reverse_sum q (-3)]
  have hs0 : Summable (fun k : ℤ => atom q (5*k+0)) :=
    (atom_summable q hq).comp_injective (affine_injective 0)
  have hs2 : Summable (fun k : ℤ => atom q (-5*k+(-3))) := by
    apply (atom_summable q hq).comp_injective
    intro i j hij
    change -5*i+(-3)= -5*j+(-3) at hij
    omega
  rw [← hs0.tsum_add hs2]
  apply tsum_congr
  intro k
  simpa only [add_zero, sub_eq_add_neg] using atom_zero_pair q k

theorem filtered_two_sum (q : ℂ) (hq : ‖q‖ < 1) :
    (∑' j : ℤ, filtered q 2 j)= -q^2*(∑' k : ℤ, term (q^5) 2 k) := by
  have he (j : ℤ) : filtered q 2 j=classTerm q (-1) j+classTerm q (-2) j := by
    simp only [filtered, classTerm, residue_two_iff]
    change (if j%5=3 ∨ j%5=4 then atom q j else 0)=
      (if j%5=4 then atom q j else 0)+(if j%5=3 then atom q j else 0)
    by_cases h3 : j%5=3 <;> by_cases h4 : j%5=4 <;> simp_all
  simp_rw [he]
  rw [(class_summable q hq (-1)).tsum_add (class_summable q hq (-2)),
    class_sum q hq (-1), class_sum q hq (-2), reverse_sum q (-2)]
  have hs1 : Summable (fun k : ℤ => atom q (5*k+(-1))) :=
    (atom_summable q hq).comp_injective (affine_injective (-1))
  have hs2 : Summable (fun k : ℤ => atom q (-5*k+(-2))) := by
    apply (atom_summable q hq).comp_injective
    intro i j hij
    change -5*i+(-2)= -5*j+(-2) at hij
    omega
  rw [← hs1.tsum_add hs2, ← tsum_mul_left]
  apply tsum_congr
  intro k
  simpa only [sub_eq_add_neg] using atom_two_pair q k

theorem filtered_zero_product (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' j : ℤ, filtered q 0 j)=
      euler (q^5)*((residue (q^5) 1*residue (q^5) 4)⁻¹)^2 := by
  rw [filtered_zero_sum q hq]
  apply WatsonQuintupleProduct.first_product (q^5) _ (pow_ne_zero _ hq0)
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)

theorem filtered_two_product (q : ℂ) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    (∑' j : ℤ, filtered q 2 j)=
      -q^2*(euler (q^5)*((residue (q^5) 2*residue (q^5) 3)⁻¹)^2) := by
  rw [filtered_two_sum q hq, WatsonQuintupleProduct.second_product (q^5) _ (pow_ne_zero _ hq0)]
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)

end
end Borwein.PentagonalOuterSum
