import Borwein.FivePoleCircle
import Mathlib.NumberTheory.ZetaValues

namespace Borwein.ResidueMultiplicity
noncomputable section
open scoped BigOperators

def centered (q : ℚ) (k : ℕ) : ℤ :=
  (k:ℤ)*q.num-round ((k:ℝ)*q)*q.den

def distance (q : ℚ) (k : ℕ) : ℕ := (centered q k).natAbs

theorem distance_eq_residue (q : ℚ) (k : ℕ) :
    (distance q k:ℝ) = DirichletCover.residue q k := by
  rw [DirichletCover.residue_eq_integer]
  change ((centered q k).natAbs:ℝ) = |(centered q k:ℝ)|
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

theorem equal_distance_divisibility (q : ℚ) (k l : ℕ)
    (he : distance q k = distance q l) :
    (q.den:ℤ) ∣ (k:ℤ)-l ∨ (q.den:ℤ) ∣ (k:ℤ)+l := by
  have ha : |centered q k| = |centered q l| := by
    have hh := congrArg (fun n : ℕ => (n:ℤ)) he
    simpa only [distance, Int.natCast_natAbs] using hh
  rcases abs_eq_abs.mp ha with hh | hh
  · left
    have hd : (q.den:ℤ) ∣ ((k:ℤ)-l)*q.num := by
      refine ⟨round ((k:ℝ)*q)-round ((l:ℝ)*q), ?_⟩
      unfold centered at hh
      nlinarith
    exact q.isCoprime_num_den.symm.dvd_of_dvd_mul_right hd
  · right
    have hd : (q.den:ℤ) ∣ ((k:ℤ)+l)*q.num := by
      refine ⟨round ((k:ℝ)*q)+round ((l:ℝ)*q), ?_⟩
      unfold centered at hh
      nlinarith
    exact q.isCoprime_num_den.symm.dvd_of_dvd_mul_right hd

theorem distance_injective_on (q : ℚ) (K : ℕ) (hK : 2*K < q.den) :
    Set.InjOn (distance q) (Set.Icc 1 K) := by
  intro k hk l hl he
  rcases hk with ⟨hk1, hkK⟩
  rcases hl with ⟨hl1, hlK⟩
  rcases equal_distance_divisibility q k l he with hd | hd
  · have hlt : |(k:ℤ)-l| < (q.den:ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
    omega
  · have hlt : |(k:ℤ)+l| < (q.den:ℤ) := by
      rw [abs_of_nonneg (by positivity)]
      omega
    have hz := Int.eq_zero_of_abs_lt_dvd hd hlt
    omega

theorem distance_positive (q : ℚ) (k : ℕ) (hk : ¬ q.den ∣ k) :
    0 < distance q k := by
  have h := DirichletCover.residue_ge_one q k hk
  rw [← distance_eq_residue] at h
  exact_mod_cast (show (0:ℝ) < distance q k by linarith)

theorem distance_positive_on (q : ℚ) (K : ℕ) (hK : 2*K < q.den)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 K) : 0 < distance q k := by
  apply distance_positive
  intro hd
  have hk' := Finset.mem_Icc.mp hk
  have hh := Nat.le_of_dvd (by omega : 0 < k) hd
  omega

theorem inverse_square_sum (q : ℚ) (K : ℕ) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(distance q k:ℝ)^2) ≤ Real.pi^2/6 := by
  have hi : ∀ k ∈ Finset.Icc 1 K, ∀ l ∈ Finset.Icc 1 K,
      distance q k = distance q l → k = l := by
    intro k hk l hl he
    exact distance_injective_on q K hK (Finset.mem_Icc.mp hk) (Finset.mem_Icc.mp hl) he
  have he : (∑ i ∈ (Finset.Icc 1 K).image (distance q), (1:ℝ)/(i:ℝ)^2) =
      ∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(distance q k:ℝ)^2 := Finset.sum_image hi
  rw [← he]
  have h := Summable.sum_le_tsum ((Finset.Icc 1 K).image (distance q))
    (fun i _ => by positivity : ∀ i ∉ (Finset.Icc 1 K).image (distance q),
      (0:ℝ) ≤ 1/(i:ℝ)^2) hasSum_zeta_two.summable
  simpa only [hasSum_zeta_two.tsum_eq] using h

theorem residue_inverse_square_sum (q : ℚ) (K : ℕ) (hK : 2*K < q.den) :
    (∑ k ∈ Finset.Icc 1 K, (1:ℝ)/(DirichletCover.residue q k)^2) ≤ Real.pi^2/6 := by
  simpa only [distance_eq_residue] using inverse_square_sum q K hK

theorem prefix_tail_disjoint (q : ℚ) (L K : ℕ) (hLK : L ≤ K) (hK : 2*K < q.den) :
    Disjoint ((Finset.Icc 1 L).image (distance q))
      ((Finset.Ioc L K).image (distance q)) := by
  apply Finset.disjoint_left.mpr
  intro r hr1 hr2
  obtain ⟨k,hk,hkr⟩ := Finset.mem_image.mp hr1
  obtain ⟨l,hl,hlr⟩ := Finset.mem_image.mp hr2
  have hk' := Finset.mem_Icc.mp hk
  have hl' := Finset.mem_Ioc.mp hl
  have he := distance_injective_on q K hK
    (show k ∈ Set.Icc 1 K by constructor <;> omega)
    (show l ∈ Set.Icc 1 K by constructor <;> omega) (hkr.trans hlr.symm)
  omega

end
end Borwein.ResidueMultiplicity
