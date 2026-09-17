import Borwein.LargeDenominatorVariation

namespace Borwein.ResidueBlockCount
noncomputable section
open scoped BigOperators
open ResidueMultiplicity

def blocks (K b : ℕ) := (K+b-1)/b
def index (q : ℚ) (k : ℕ) := (k-1)/q.den

theorem index_bounds (q : ℚ) (k : ℕ) (hk : 0 < k) :
    index q k*q.den < k ∧ k ≤ (index q k+1)*q.den := by
  have hm := Nat.mod_lt (k-1) q.pos
  have he := Nat.mod_add_div (k-1) q.den
  rw [Nat.mul_comm q.den] at he
  unfold index
  constructor
  · omega
  · rw [Nat.add_mul,one_mul]
    omega

theorem index_lt_blocks (q : ℚ) (K k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
    index q k < blocks K q.den := by
  have hk' := Finset.mem_Icc.mp hk
  have hK : 0 < K := by omega
  have he : K+q.den-1 = (K-1)+q.den := by omega
  unfold blocks index
  rw [he, Nat.add_div_right _ q.pos]
  have h : (k-1)/q.den ≤ (K-1)/q.den := Nat.div_le_div_right (show k-1 ≤ K-1 by omega)
  omega

theorem centered_injective_block (q : ℚ) (t : ℕ) :
    Set.InjOn (centered q) (Set.Ioc (t*q.den) ((t+1)*q.den)) := by
  intro k hk l hl he
  have hd : (q.den:ℤ) ∣ ((k:ℤ)-l)*q.num := by
    refine ⟨round ((k:ℝ)*q)-round ((l:ℝ)*q), ?_⟩
    unfold centered at he
    nlinarith
  have hd' := q.isCoprime_num_den.symm.dvd_of_dvd_mul_right hd
  rcases hk with ⟨hk1,hk2⟩
  rcases hl with ⟨hl1,hl2⟩
  have hupper : (t+1)*q.den = t*q.den+q.den := by ring
  have hlt : |(k:ℤ)-l| < (q.den:ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hz := Int.eq_zero_of_abs_lt_dvd hd' hlt
  omega

theorem encoding_injective (q : ℚ) (K : ℕ) :
    Set.InjOn (fun k => (centered q k,index q k)) (Set.Icc 1 K) := by
  intro k hk l hl he
  have hc := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  have hk' := index_bounds q k (by rcases hk with ⟨hk1,_⟩; omega)
  have hl' := index_bounds q l (by rcases hl with ⟨hl1,_⟩; omega)
  change index q k = index q l at hi
  rw [← hi] at hl'
  exact centered_injective_block q (index q k) hk' hl' hc

theorem fiber_card_le (q : ℚ) (K r : ℕ) :
    ((Finset.Icc 1 K).filter (fun k => distance q k = r)).card ≤ 2*blocks K q.den := by
  let s := (Finset.Icc 1 K).filter (fun k => distance q k = r)
  let f := fun k => (centered q k,index q k)
  have hi : Set.InjOn f s := by
    intro k hk l hl he
    exact encoding_injective q K (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1)
      (Finset.mem_Icc.mp (Finset.mem_filter.mp hl).1) he
  have hsub : s.image f ⊆ ({(r:ℤ),-(r:ℤ)} : Finset ℤ) ×ˢ Finset.range (blocks K q.den) := by
    intro p hp
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hp
    have hk' := Finset.mem_filter.mp hk
    apply Finset.mem_product.mpr
    constructor
    · have he : |centered q k| = |(r:ℤ)| := by
        have hc := congrArg (fun n : ℕ => (n:ℤ)) hk'.2
        simpa only [distance, Int.natCast_natAbs,abs_of_nonneg (Int.natCast_nonneg r)] using hc
      rcases abs_eq_abs.mp he with h | h
      · simp only [f,Finset.mem_insert,Finset.mem_singleton]; exact Or.inl h
      · simp only [f,Finset.mem_insert,Finset.mem_singleton]; exact Or.inr h
    · exact Finset.mem_range.mpr (index_lt_blocks q K k hk'.1)
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hi, Finset.card_product, Finset.card_range] at h
  have hc : ({(r:ℤ),-(r:ℤ)} : Finset ℤ).card ≤ 2 := by
    exact Finset.card_le_two
  exact h.trans (Nat.mul_le_mul_right _ hc)

theorem inverse_square_sum (q : ℚ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(distance q k:ℝ)^2) ≤
      (2*blocks K q.den:ℕ)*(Real.pi^2/6) := by
  let s := Finset.Icc 1 K
  let t := s.image (distance q)
  have he := Finset.sum_fiberwise_of_maps_to' (s := s) (t := t)
    (fun k hk => Finset.mem_image_of_mem (distance q) hk)
    (fun r : ℕ => (1:ℝ)/(r:ℝ)^2)
  simp only [Finset.sum_const, nsmul_eq_mul] at he
  rw [← he]
  have h := Finset.sum_le_sum (s := t) (fun r _ =>
    mul_le_mul_of_nonneg_right
      (show (((s.filter (fun k => distance q k = r)).card):ℝ) ≤ (2*blocks K q.den:ℕ) by
        exact_mod_cast fiber_card_le q K r)
      (show (0:ℝ) ≤ 1/(r:ℝ)^2 by positivity))
  rw [← Finset.mul_sum] at h
  have hs := Summable.sum_le_tsum t (fun r _ => show (0:ℝ) ≤ 1/(r:ℝ)^2 by positivity)
    hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq] at hs
  exact h.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))

theorem residue_inverse_square_sum (q : ℚ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(DirichletCover.residue q k)^2) ≤
      (2*blocks K q.den:ℕ)*(Real.pi^2/6) := by
  simpa only [distance_eq_residue] using inverse_square_sum q K

theorem nonresonant_inverse_square_sum (q : ℚ) (K : ℕ) :
    (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ k),
      (1:ℝ)/(DirichletCover.residue q k)^2) ≤
      (2*blocks K q.den:ℕ)*(Real.pi^2/6) := by
  refine le_trans ?_ (residue_inverse_square_sum q K)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun k _ _ => by positivity)

end
end Borwein.ResidueBlockCount
