import Borwein.ZeroPoleBudget

namespace Borwein.ShiftedResidues
noncomputable section
open scoped BigOperators

def phase (q : ℚ) (k : ℕ) (j : Fin 4) : ℝ :=
  (k:ℝ)*q+(j.val+1)/5

def centered (q : ℚ) (k : ℕ) (j : Fin 4) : ℤ :=
  5*(k:ℤ)*q.num+(j.val+1)*q.den-5*q.den*round (phase q k j)

def distance (q : ℚ) (k : ℕ) (j : Fin 4) : ℕ := (centered q k j).natAbs

theorem distance_eq (q : ℚ) (k : ℕ) (j : Fin 4) :
    (distance q k j:ℝ) = 5*q.den*|phase q k j-round (phase q k j)| := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  change ((centered q k j).natAbs:ℝ) = _
  rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs,
    ← abs_of_pos (show (0:ℝ) < 5*q.den by positivity), ← abs_mul]
  congr 1
  unfold centered phase
  push_cast
  rw [Rat.cast_def]
  field_simp

theorem non_five_divisible (q : ℚ) (hb5 : q.den.Coprime 5) (k : ℕ) (j : Fin 4) :
    ¬ 5 ∣ distance q k j := by
  intro hd
  have hc : (5:ℤ) ∣ centered q k j := by
    have hn : (5:ℤ) ∣ (distance q k j:ℤ) := by exact_mod_cast hd
    simpa only [distance, Int.natCast_natAbs, dvd_abs] using hn
  have hj : (5:ℤ) ∣ ((j.val:ℤ)+1)*q.den := by
    have hh := dvd_sub hc (show (5:ℤ) ∣ 5*(k:ℤ)*q.num-5*q.den*round (phase q k j) by
      apply dvd_sub <;> ring_nf <;> omega)
    have he : centered q k j-(5*(k:ℤ)*q.num-5*q.den*round (phase q k j)) =
        ((j.val:ℤ)+1)*q.den := by unfold centered; ring
    rwa [he] at hh
  have hcop : IsCoprime (5:ℤ) (q.den:ℤ) := hb5.symm.isCoprime
  have hj' := hcop.dvd_of_dvd_mul_right hj
  have hjlt : |(j.val:ℤ)+1| < 5 := by
    rw [abs_of_nonneg (by positivity)]
    have h := j.isLt
    omega
  have hz := Int.eq_zero_of_abs_lt_dvd hj' hjlt
  omega

theorem distance_positive (q : ℚ) (hb5 : q.den.Coprime 5) (k : ℕ) (j : Fin 4) :
    0 < distance q k j := by
  have h := non_five_divisible q hb5 k j
  by_contra hp
  have hz : distance q k j = 0 := by omega
  exact h (hz ▸ dvd_zero 5)

theorem joint_injective (q : ℚ) (hb5 : q.den.Coprime 5) (K : ℕ) (hK : 2*K < q.den)
    (k l : ℕ) (hk : k ∈ Finset.Icc 1 K) (hl : l ∈ Finset.Icc 1 K)
    (j i : Fin 4) (he : distance q k j = distance q l i) : k = l ∧ j = i := by
  have ha : |centered q k j| = |centered q l i| := by
    have h := congrArg (fun n : ℕ => (n:ℤ)) he
    simpa only [distance, Int.natCast_natAbs] using h
  have hcop : IsCoprime (q.den:ℤ) (5*q.num) :=
    hb5.isCoprime.mul_right q.isCoprime_num_den.symm
  have hk' := Finset.mem_Icc.mp hk
  have hl' := Finset.mem_Icc.mp hl
  rcases abs_eq_abs.mp ha with hh | hh
  · have hd : (q.den:ℤ) ∣ ((k:ℤ)-l)*(5*q.num) := by
      refine ⟨5*(round (phase q k j)-round (phase q l i))-((j.val:ℤ)-i.val), ?_⟩
      unfold centered at hh
      nlinarith
    have hd' := hcop.dvd_of_dvd_mul_right hd
    have he0 := Int.eq_zero_of_abs_lt_dvd hd'
      (show |(k:ℤ)-l| < (q.den:ℤ) by rw [abs_lt]; constructor <;> omega)
    have hkl : k = l := by omega
    subst l
    refine ⟨rfl, ?_⟩
    have hden : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_nz
    have hij : (j.val:ℤ)-i.val = 5*(round (phase q k j)-round (phase q k i)) := by
      apply mul_left_cancel₀ hden
      unfold centered at hh
      nlinarith
    have hdiv : (5:ℤ) ∣ (j.val:ℤ)-i.val := ⟨_,hij⟩
    have hj := j.isLt
    have hi := i.isLt
    have hzero := Int.eq_zero_of_abs_lt_dvd hdiv
      (show |(j.val:ℤ)-i.val| < 5 by rw [abs_lt]; constructor <;> omega)
    apply Fin.ext
    omega
  · have hd : (q.den:ℤ) ∣ ((k:ℤ)+l)*(5*q.num) := by
      refine ⟨5*(round (phase q k j)+round (phase q l i))-((j.val:ℤ)+i.val+2), ?_⟩
      unfold centered at hh
      nlinarith
    have hd' := hcop.dvd_of_dvd_mul_right hd
    have he0 := Int.eq_zero_of_abs_lt_dvd hd'
      (show |(k:ℤ)+l| < (q.den:ℤ) by rw [abs_of_nonneg (by positivity)]; omega)
    omega

end
end Borwein.ShiftedResidues
