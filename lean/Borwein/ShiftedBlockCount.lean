import Borwein.ResidueBlockCount

namespace Borwein.ShiftedBlockCount
noncomputable section
open scoped BigOperators
open ShiftedResidues
open ResidueBlockCount (blocks index)

theorem centered_injective_block (q : ℚ) (hb5 : q.den.Coprime 5) (t : ℕ)
    (k l : ℕ) (hk : k ∈ Set.Ioc (t*q.den) ((t+1)*q.den))
    (hl : l ∈ Set.Ioc (t*q.den) ((t+1)*q.den)) (j i : Fin 4)
    (he : centered q k j = centered q l i) : k = l ∧ j = i := by
  have hcop : IsCoprime (q.den:ℤ) (5*q.num) :=
    hb5.isCoprime.mul_right q.isCoprime_num_den.symm
  have hd : (q.den:ℤ) ∣ ((k:ℤ)-l)*(5*q.num) := by
    refine ⟨5*(round (phase q k j)-round (phase q l i))-((j.val:ℤ)-i.val), ?_⟩
    unfold centered at he
    nlinarith
  have hd' := hcop.dvd_of_dvd_mul_right hd
  rcases hk with ⟨hk1,hk2⟩
  rcases hl with ⟨hl1,hl2⟩
  have hupper : (t+1)*q.den = t*q.den+q.den := by ring
  have hz := Int.eq_zero_of_abs_lt_dvd hd'
    (show |(k:ℤ)-l| < (q.den:ℤ) by rw [abs_lt]; constructor <;> omega)
  have hkl : k = l := by omega
  subst l
  refine ⟨rfl, ?_⟩
  have hden : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_nz
  have hij : (j.val:ℤ)-i.val = 5*(round (phase q k j)-round (phase q k i)) := by
    apply mul_left_cancel₀ hden
    unfold centered at he
    nlinarith
  have hdiv : (5:ℤ) ∣ (j.val:ℤ)-i.val := ⟨_,hij⟩
  have hj := j.isLt
  have hi := i.isLt
  have hzero := Int.eq_zero_of_abs_lt_dvd hdiv
    (show |(j.val:ℤ)-i.val| < 5 by rw [abs_lt]; constructor <;> omega)
  apply Fin.ext
  omega

theorem encoding_injective (q : ℚ) (hb5 : q.den.Coprime 5) (K : ℕ) :
    Set.InjOn (fun p : ℕ × Fin 4 => (centered q p.1 p.2,index q p.1))
      (↑((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))) : Set (ℕ × Fin 4)) := by
  intro p hp v hv he
  have hp' := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
  have hv' := Finset.mem_Icc.mp (Finset.mem_product.mp hv).1
  have hc := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  change index q p.1 = index q v.1 at hi
  have hpB := ResidueBlockCount.index_bounds q p.1 (by omega)
  have hvB := ResidueBlockCount.index_bounds q v.1 (by omega)
  rw [← hi] at hvB
  have h := centered_injective_block q hb5 (index q p.1) p.1 v.1 hpB hvB p.2 v.2 hc
  exact Prod.ext h.1 h.2

theorem fiber_card_le (q : ℚ) (hb5 : q.den.Coprime 5) (K r : ℕ) :
    (((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))).filter
      (fun p => distance q p.1 p.2 = r)).card ≤ 2*blocks K q.den := by
  let s := ((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))).filter
    (fun p => distance q p.1 p.2 = r)
  let f := fun p : ℕ × Fin 4 => (centered q p.1 p.2,index q p.1)
  have hi : Set.InjOn f s := by
    intro p hp v hv he
    exact encoding_injective q hb5 K (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hv).1 he
  have hsub : s.image f ⊆ ({(r:ℤ),-(r:ℤ)} : Finset ℤ) ×ˢ Finset.range (blocks K q.den) := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_product.mpr
    constructor
    · have he : |centered q p.1 p.2| = |(r:ℤ)| := by
        have hc := congrArg (fun n : ℕ => (n:ℤ)) hp'.2
        simpa only [distance, Int.natCast_natAbs,abs_of_nonneg (Int.natCast_nonneg r)] using hc
      rcases abs_eq_abs.mp he with h | h
      · simp only [f,Finset.mem_insert,Finset.mem_singleton]; exact Or.inl h
      · simp only [f,Finset.mem_insert,Finset.mem_singleton]; exact Or.inr h
    · exact Finset.mem_range.mpr (ResidueBlockCount.index_lt_blocks q K p.1
        (Finset.mem_product.mp hp'.1).1)
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hi, Finset.card_product, Finset.card_range] at h
  exact h.trans (Nat.mul_le_mul_right _ Finset.card_le_two)

theorem inverse_square_sum (q : ℚ) (hb5 : q.den.Coprime 5) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, (1:ℝ)/(distance q k j:ℝ)^2) ≤
      (2*blocks K q.den:ℕ)*((24/25:ℝ)*(Real.pi^2/6)) := by
  let s := (Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))
  let f := fun p : ℕ × Fin 4 => distance q p.1 p.2
  let t := s.image f
  have he := Finset.sum_fiberwise_of_maps_to' (s := s) (t := t)
    (fun p hp => Finset.mem_image_of_mem f hp)
    (fun r : ℕ => (1:ℝ)/(r:ℝ)^2)
  simp only [Finset.sum_const, nsmul_eq_mul] at he
  have h := Finset.sum_le_sum (s := t) (fun r _ =>
    mul_le_mul_of_nonneg_right
      (show (((s.filter (fun p => f p = r)).card):ℝ) ≤ (2*blocks K q.den:ℕ) by
        exact_mod_cast fiber_card_le q hb5 K r)
      (show (0:ℝ) ≤ 1/(r:ℝ)^2 by positivity))
  rw [← Finset.mul_sum] at h
  have hs := NonFiveSquareSum.finite_sum_le t (by
    intro r hr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hr
    exact non_five_divisible q hb5 p.1 p.2)
  have hfinal := h.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [he] at hfinal
  simpa only [s,f,Finset.sum_product] using hfinal

end
end Borwein.ShiftedBlockCount
