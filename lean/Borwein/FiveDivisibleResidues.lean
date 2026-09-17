import Borwein.GeneralDenominatorVariation

namespace Borwein.FiveDivisibleResidues
noncomputable section
open scoped BigOperators
open ShiftedResidues (phase)
open ResidueBlockCount (blocks)

def centered (q : ℚ) (B k : ℕ) (j : Fin 4) : ℤ :=
  (k:ℤ)*q.num+(j.val+1)*B-q.den*round (phase q k j)

def distance (q : ℚ) (B k : ℕ) (j : Fin 4) : ℕ := (centered q B k j).natAbs

def index (B k : ℕ) := (k-1)/B

theorem period_pos (q : ℚ) (B : ℕ) (hb : q.den = 5*B) : 0 < B := by
  have h := q.pos
  omega

theorem period_coprime (q : ℚ) (B : ℕ) (hb : q.den = 5*B) :
    IsCoprime (B:ℤ) q.num := by
  apply q.isCoprime_num_den.symm.of_isCoprime_of_dvd_left
  refine ⟨5, ?_⟩
  exact_mod_cast (show q.den = B*5 by omega)

theorem resonance_iff (q : ℚ) (B k : ℕ) (hb : q.den = 5*B) :
    q.den ∣ 5*k ↔ B ∣ k := by
  rw [hb]
  exact mul_dvd_mul_iff_left (by norm_num : (5:ℕ) ≠ 0)

theorem distance_eq (q : ℚ) (B k : ℕ) (hb : q.den = 5*B) (j : Fin 4) :
    (distance q B k j:ℝ) = q.den*|phase q k j-round (phase q k j)| := by
  have hp : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hB : (q.den:ℝ) = 5*B := by exact_mod_cast hb
  change ((centered q B k j).natAbs:ℝ) = _
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs,
    ← abs_of_pos hp, ← abs_mul]
  congr 1
  unfold centered phase
  push_cast
  rw [Rat.cast_def]
  field_simp
  nlinarith

theorem distance_positive (q : ℚ) (B k : ℕ) (hb : q.den = 5*B)
    (hk : ¬ B ∣ k) (j : Fin 4) : 0 < distance q B k j := by
  by_contra hn
  have hz : centered q B k j = 0 := by
    have hd : (centered q B k j).natAbs = 0 := by change distance q B k j = 0; omega
    exact Int.natAbs_eq_zero.mp hd
  have hb' : (q.den:ℤ) = 5*B := by exact_mod_cast hb
  have hd : (B:ℤ) ∣ (k:ℤ)*q.num := by
    refine ⟨5*round (phase q k j)-((j.val:ℤ)+1), ?_⟩
    unfold centered at hz
    rw [hb'] at hz
    nlinarith
  have hk' := (period_coprime q B hb).dvd_of_dvd_mul_right hd
  exact hk (by exact_mod_cast hk')

theorem index_bounds (B k : ℕ) (hB : 0 < B) (hk : 0 < k) :
    index B k*B < k ∧ k ≤ (index B k+1)*B := by
  have hm := Nat.mod_lt (k-1) hB
  have he := Nat.mod_add_div (k-1) B
  rw [Nat.mul_comm B] at he
  unfold index
  constructor
  · omega
  · rw [Nat.add_mul,one_mul]
    omega

theorem index_lt_blocks (B K k : ℕ) (hB : 0 < B) (hk : k ∈ Finset.Icc 1 K) :
    index B k < blocks K B := by
  have hk' := Finset.mem_Icc.mp hk
  have he : K+B-1 = (K-1)+B := by omega
  unfold blocks index
  rw [he, Nat.add_div_right _ hB]
  have h : (k-1)/B ≤ (K-1)/B := Nat.div_le_div_right (show k-1 ≤ K-1 by omega)
  omega

theorem centered_injective_block (q : ℚ) (B : ℕ) (hb : q.den = 5*B) (t : ℕ)
    (k l : ℕ) (hk : k ∈ Set.Ioc (t*B) ((t+1)*B))
    (hl : l ∈ Set.Ioc (t*B) ((t+1)*B)) (j i : Fin 4)
    (he : centered q B k j = centered q B l i) : k = l ∧ j = i := by
  have hb' : (q.den:ℤ) = 5*B := by exact_mod_cast hb
  have hd : (B:ℤ) ∣ ((k:ℤ)-l)*q.num := by
    refine ⟨5*(round (phase q k j)-round (phase q l i))-((j.val:ℤ)-i.val), ?_⟩
    unfold centered at he
    rw [hb'] at he
    nlinarith
  have hd' := (period_coprime q B hb).dvd_of_dvd_mul_right hd
  rcases hk with ⟨hk1,hk2⟩
  rcases hl with ⟨hl1,hl2⟩
  have hupper : (t+1)*B = t*B+B := by ring
  have hz := Int.eq_zero_of_abs_lt_dvd hd'
    (show |(k:ℤ)-l| < (B:ℤ) by rw [abs_lt]; constructor <;> omega)
  have hkl : k = l := by omega
  subst l
  refine ⟨rfl, ?_⟩
  have hB : (B:ℤ) ≠ 0 := by exact_mod_cast (period_pos q B hb).ne'
  have hij : (j.val:ℤ)-i.val = 5*(round (phase q k j)-round (phase q k i)) := by
    apply mul_left_cancel₀ hB
    unfold centered at he
    rw [hb'] at he
    nlinarith
  have hdiv : (5:ℤ) ∣ (j.val:ℤ)-i.val := ⟨_,hij⟩
  have hj := j.isLt
  have hi := i.isLt
  have hzero := Int.eq_zero_of_abs_lt_dvd hdiv
    (show |(j.val:ℤ)-i.val| < 5 by rw [abs_lt]; constructor <;> omega)
  apply Fin.ext
  omega

theorem encoding_injective (q : ℚ) (B : ℕ) (hb : q.den = 5*B) (K : ℕ) :
    Set.InjOn (fun p : ℕ × Fin 4 => (centered q B p.1 p.2,index B p.1))
      (↑((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))) : Set (ℕ × Fin 4)) := by
  intro p hp v hv he
  have hp' := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
  have hv' := Finset.mem_Icc.mp (Finset.mem_product.mp hv).1
  have hc := congrArg Prod.fst he
  have hi := congrArg Prod.snd he
  change index B p.1 = index B v.1 at hi
  have hpB := index_bounds B p.1 (period_pos q B hb) (by omega)
  have hvB := index_bounds B v.1 (period_pos q B hb) (by omega)
  rw [← hi] at hvB
  have h := centered_injective_block q B hb (index B p.1) p.1 v.1 hpB hvB p.2 v.2 hc
  exact Prod.ext h.1 h.2

theorem fiber_card_le (q : ℚ) (B : ℕ) (hb : q.den = 5*B) (K r : ℕ) :
    (((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))).filter
      (fun p => distance q B p.1 p.2 = r)).card ≤ 2*blocks K B := by
  let s := ((Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))).filter
    (fun p => distance q B p.1 p.2 = r)
  let f := fun p : ℕ × Fin 4 => (centered q B p.1 p.2,index B p.1)
  have hi : Set.InjOn f s := by
    intro p hp v hv he
    exact encoding_injective q B hb K (Finset.mem_filter.mp hp).1
      (Finset.mem_filter.mp hv).1 he
  have hsub : s.image f ⊆ ({(r:ℤ),-(r:ℤ)} : Finset ℤ) ×ˢ Finset.range (blocks K B) := by
    intro v hv
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    have hp' := Finset.mem_filter.mp hp
    apply Finset.mem_product.mpr
    constructor
    · have he : |centered q B p.1 p.2| = |(r:ℤ)| := by
        have hc := congrArg (fun n : ℕ => (n:ℤ)) hp'.2
        simpa only [distance, Int.natCast_natAbs,abs_of_nonneg (Int.natCast_nonneg r)] using hc
      rcases abs_eq_abs.mp he with h | h
      · simp only [f,Finset.mem_insert,Finset.mem_singleton]; exact Or.inl h
      · simp only [f,Finset.mem_insert,Finset.mem_singleton]; exact Or.inr h
    · exact Finset.mem_range.mpr (index_lt_blocks B K p.1 (period_pos q B hb)
        (Finset.mem_product.mp hp'.1).1)
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hi, Finset.card_product, Finset.card_range] at h
  exact h.trans (Nat.mul_le_mul_right _ Finset.card_le_two)

theorem inverse_square_sum (q : ℚ) (B : ℕ) (hb : q.den = 5*B) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, ∑ j : Fin 4, (1:ℝ)/(distance q B k j:ℝ)^2) ≤
      (2*blocks K B:ℕ)*(Real.pi^2/6) := by
  let s := (Finset.Icc 1 K) ×ˢ (Finset.univ : Finset (Fin 4))
  let f := fun p : ℕ × Fin 4 => distance q B p.1 p.2
  let t := s.image f
  have he := Finset.sum_fiberwise_of_maps_to' (s := s) (t := t)
    (fun p hp => Finset.mem_image_of_mem f hp)
    (fun r : ℕ => (1:ℝ)/(r:ℝ)^2)
  simp only [Finset.sum_const, nsmul_eq_mul] at he
  have h := Finset.sum_le_sum (s := t) (fun r _ =>
    mul_le_mul_of_nonneg_right
      (show (((s.filter (fun p => f p = r)).card):ℝ) ≤ (2*blocks K B:ℕ) by
        exact_mod_cast fiber_card_le q B hb K r)
      (show (0:ℝ) ≤ 1/(r:ℝ)^2 by positivity))
  rw [← Finset.mul_sum] at h
  have hs := Summable.sum_le_tsum t (fun r _ => show (0:ℝ) ≤ 1/(r:ℝ)^2 by positivity)
    hasSum_zeta_two.summable
  rw [hasSum_zeta_two.tsum_eq] at hs
  have hfinal := h.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [he] at hfinal
  simpa only [s,f,Finset.sum_product] using hfinal

end
end Borwein.FiveDivisibleResidues
