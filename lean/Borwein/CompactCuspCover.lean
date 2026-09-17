import Borwein.DirichletCover

namespace Borwein.CompactCuspCover
noncomputable section
open Set DirichletCover

def candidates (Q : ℕ) : Finset ℚ :=
  (Finset.Icc 1 Q).biUnion (fun b => (Finset.Icc (0:ℤ) (b:ℤ)).image (fun a : ℤ => (a:ℚ)/(b:ℚ)))

theorem numerator_error (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q) (q : ℚ) (hq : Near ξ Q q) :
    |(q.den:ℝ)*ξ-q.num| ≤ 1/(Q:ℝ) := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have he : (q.den:ℝ)*(ξ-q) = (q.den:ℝ)*ξ-q.num := by
    rw [Rat.cast_def]
    field_simp
  calc
    _ = (q.den:ℝ)*|ξ-q| := by rw [← he,abs_mul,abs_of_pos hb]
    _ ≤ (q.den:ℝ)*(1/((q.den:ℝ)*Q)) := mul_le_mul_of_nonneg_left hq.2 hb.le
    _ = _ := by field_simp

theorem numerator_bounds (ξ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (q : ℚ)
    (hq : Near ξ Q q) (hξ : ξ ∈ Icc (0:ℝ) 1) : 0 ≤ q.num ∧ q.num ≤ q.den := by
  have hQr : (1:ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
  have he := abs_le.mp (numerator_error ξ Q (by omega) q hq)
  have ht : 1/(Q:ℝ) < 1 := (div_lt_one (by positivity)).mpr hQr
  have hb : (0:ℝ) ≤ q.den := Nat.cast_nonneg _
  constructor
  · by_contra h
    have hni : q.num ≤ -1 := by omega
    have hnr : (q.num:ℝ) ≤ -1 := by exact_mod_cast hni
    nlinarith [mul_nonneg hb hξ.1]
  · by_contra h
    have hni : (q.den:ℤ)+1 ≤ q.num := by omega
    have hnr : (q.den:ℝ)+1 ≤ q.num := by exact_mod_cast hni
    nlinarith [mul_le_mul_of_nonneg_left hξ.2 hb]

theorem mem_candidates (ξ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (q : ℚ)
    (hq : Near ξ Q q) (hξ : ξ ∈ Icc (0:ℝ) 1) : q ∈ candidates Q := by
  have hn := numerator_bounds ξ Q hQ q hq hξ
  apply Finset.mem_biUnion.mpr
  refine ⟨q.den,Finset.mem_Icc.mpr ⟨q.pos,hq.1⟩,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨q.num,Finset.mem_Icc.mpr hn,?_⟩
  exact Rat.num_div_den q

theorem exists_candidate (ξ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (hξ : ξ ∈ Icc (0:ℝ) 1) :
    ∃ q ∈ candidates Q, Near ξ Q q := by
  obtain ⟨q,hq⟩ := exists_near ξ Q (by omega)
  exact ⟨q,mem_candidates ξ Q hQ q hq hξ,hq⟩

theorem denominator_one (ξ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (q : ℚ)
    (hq : Near ξ Q q) (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : q.den = 1) : q = 0 ∨ q = 1 := by
  have hn := numerator_bounds ξ Q hQ q hq hξ
  rw [hb] at hn
  have hnum : q.num = 0 ∨ q.num = 1 := by omega
  rcases hnum with hnum | hnum
  · left
    rw [← Rat.num_div_den q,hnum,hb]
    norm_num
  · right
    rw [← Rat.num_div_den q,hnum,hb]
    norm_num

theorem denominator_five_numerator (ξ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (q : ℚ)
    (hq : Near ξ Q q) (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : q.den = 5) :
    1 ≤ q.num ∧ q.num ≤ 4 := by
  have hn := numerator_bounds ξ Q hQ q hq hξ
  rw [hb] at hn
  have hc := q.reduced
  rw [hb] at hc
  have h0 : q.num ≠ 0 := by intro h; simp [h] at hc
  have h5 : q.num ≠ 5 := by intro h; norm_num [h] at hc
  omega

theorem denominator_five (ξ : ℝ) (Q : ℕ) (hQ : 2 ≤ Q) (q : ℚ)
    (hq : Near ξ Q q) (hξ : ξ ∈ Icc (0:ℝ) 1) (hb : q.den = 5) :
    ∃ j : Fin 4, q = ((j.val+1:ℕ):ℚ)/5 := by
  have hn := denominator_five_numerator ξ Q hQ q hq hξ hb
  let j : Fin 4 := ⟨(q.num-1).toNat,by omega⟩
  refine ⟨j,?_⟩
  have hj : (j.val+1:ℤ) = q.num := by dsimp [j]; omega
  rw [← Rat.num_div_den q,hb,← hj]
  push_cast
  rfl

end
end Borwein.CompactCuspCover
