import Borwein.ShiftedResidues

namespace Borwein.NonFiveSquareSum
noncomputable section
open scoped BigOperators

def multiples (n : ℕ) : ℝ := if 5 ∣ n then 1/(n:ℝ)^2 else 0
def nonmultiples (n : ℕ) : ℝ := if 5 ∣ n then 0 else 1/(n:ℝ)^2

theorem multiples_hasSum : HasSum multiples ((1/25:ℝ)*(Real.pi^2/6)) := by
  have hi : Function.Injective (fun n : ℕ => 5*n) := by
    intro m n h
    change 5*m = 5*n at h
    omega
  apply (hi.hasSum_iff (f := multiples) (by
    intro n hn
    have hd : ¬ 5 ∣ n := by
      rintro ⟨m,hm⟩
      exact hn ⟨m,hm.symm⟩
    simp [multiples,hd])).mp
  have h := hasSum_zeta_two.mul_left (1/25:ℝ)
  apply h.congr_fun
  intro n
  simp only [Function.comp_apply, multiples, dvd_mul_right, if_true, Nat.cast_mul,
    Nat.cast_ofNat, mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem nonmultiples_hasSum :
    HasSum nonmultiples ((24/25:ℝ)*(Real.pi^2/6)) := by
  have h := hasSum_zeta_two.sub multiples_hasSum
  have he : Real.pi^2/6-(1/25:ℝ)*(Real.pi^2/6) = (24/25:ℝ)*(Real.pi^2/6) := by ring
  rw [he] at h
  apply h.congr_fun
  intro n
  by_cases hn : 5 ∣ n <;> simp [nonmultiples,multiples,hn]

theorem finite_sum_le (s : Finset ℕ) (hs : ∀ n ∈ s, ¬ 5 ∣ n) :
    (∑ n ∈ s, (1:ℝ)/(n:ℝ)^2) ≤ (24/25:ℝ)*(Real.pi^2/6) := by
  have h := Summable.sum_le_tsum s
    (fun n _ => show 0 ≤ nonmultiples n by unfold nonmultiples; split_ifs <;> positivity)
    nonmultiples_hasSum.summable
  rw [nonmultiples_hasSum.tsum_eq] at h
  have he : (∑ n ∈ s, nonmultiples n) = ∑ n ∈ s, (1:ℝ)/(n:ℝ)^2 := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [nonmultiples,hs n hn]
  rwa [he] at h

theorem shifted_inverse_square_sum (q : ℚ) (hb5 : q.den.Coprime 5)
    (K : ℕ) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, (1:ℝ)/(ShiftedResidues.distance q k j:ℝ)^2) ≤
      (24/25:ℝ)*(Real.pi^2/6) := by
  let s := (Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))
  let f := fun p : ℕ × Fin 4 => ShiftedResidues.distance q p.1 p.2
  have hi : ∀ p ∈ s, ∀ t ∈ s, f p = f t → p = t := by
    intro p hp t ht he
    have hp' := (Finset.mem_product.mp hp).1
    have ht' := (Finset.mem_product.mp ht).1
    have h := ShiftedResidues.joint_injective q hb5 K hK p.1 t.1 hp' ht' p.2 t.2 he
    exact Prod.ext h.1 h.2
  have h := finite_sum_le (s.image f) (by
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact ShiftedResidues.non_five_divisible q hb5 p.1 p.2)
  have he : (∑ n ∈ s.image f, (1:ℝ)/(n:ℝ)^2) =
      ∑ p ∈ s, (1:ℝ)/(f p:ℝ)^2 := Finset.sum_image hi
  rw [he] at h
  simpa only [s,f,Finset.sum_product] using h

end
end Borwein.NonFiveSquareSum
