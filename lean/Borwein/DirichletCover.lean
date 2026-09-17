import Borwein.FiniteFourierKernel
import Mathlib.NumberTheory.DiophantineApproximation.Basic

namespace Borwein.DirichletCover
noncomputable section

/-- A reduced rational cusp; its denominator is intrinsic to `q`. -/
def Near (ξ : ℝ) (Q : ℕ) (q : ℚ) : Prop :=
  q.den ≤ Q ∧ |ξ-(q:ℝ)| ≤ 1/((q.den:ℝ)*Q)

theorem exists_near (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ q : ℚ, Near ξ Q q := by
  obtain ⟨q, hq, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le ξ hQ
  refine ⟨q, hden, hq.trans ?_⟩
  apply one_div_le_one_div_of_le
  · exact mul_pos (Nat.cast_pos.mpr q.pos) (Nat.cast_pos.mpr hQ)
  · nlinarith [show (0:ℝ) ≤ q.den by positivity]

theorem scaled_error (ξ : ℝ) (Q : ℕ) (q : ℚ) (h : Near ξ Q q) (k : ℕ) :
    |(k:ℝ)*ξ-k*q| ≤ k/((q.den:ℝ)*Q) := by
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg k)

theorem integer_distance_lower (ξ : ℝ) (Q : ℕ) (q : ℚ) (h : Near ξ Q q)
    (k : ℕ) (m : ℤ) :
    |(k:ℝ)*q-m| - k/((q.den:ℝ)*Q) ≤ |(k:ℝ)*ξ-m| := by
  have ht := abs_add_le ((k:ℝ)*q-k*ξ) ((k:ℝ)*ξ-m)
  have he := scaled_error ξ Q q h k
  rw [abs_sub_comm ((k:ℝ)*q) (k*ξ)] at ht
  have hid : (k:ℝ)*q-k*ξ+(k*ξ-m) = k*q-m := by ring
  rw [hid] at ht
  linarith

/-- The manuscript's local coordinate at a rational cusp. -/
def localAngle (n : ℕ) (θ : ℝ) (q : ℚ) :=
  5*(n:ℝ)*(θ-2*Real.pi*q)

theorem localAngle_bound (n Q : ℕ) (θ : ℝ) (q : ℚ)
    (h : Near (θ/(2*Real.pi)) Q q) :
    |localAngle n θ q| ≤ 10*Real.pi*n/((q.den:ℝ)*Q) := by
  have hp : 0 < 2*Real.pi := by positivity
  have hid : θ-2*Real.pi*(q:ℝ) = (2*Real.pi)*(θ/(2*Real.pi)-q) := by
    field_simp
  unfold localAngle
  rw [hid, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 5*n by positivity),
    abs_mul, abs_of_pos hp]
  have hh := mul_le_mul_of_nonneg_left h.2
    (by positivity : (0:ℝ) ≤ (5*n)*(2*Real.pi))
  have heq : (5*(n:ℝ))*(2*Real.pi)*(1/((q.den:ℝ)*Q)) =
      10*Real.pi*n/((q.den:ℝ)*Q) := by ring
  rw [heq] at hh
  simpa only [mul_assoc] using hh

theorem exists_localAngle (n Q : ℕ) (θ : ℝ) (hQ : 0 < Q) :
    ∃ q : ℚ, Near (θ/(2*Real.pi)) Q q ∧
      |localAngle n θ q| ≤ 10*Real.pi*n/((q.den:ℝ)*Q) := by
  obtain ⟨q,hq⟩ := exists_near (θ/(2*Real.pi)) Q hQ
  exact ⟨q,hq,localAngle_bound n Q θ q hq⟩

theorem rational_nonresonant (q : ℚ) (k : ℕ) (hk : ¬ q.den ∣ k) (m : ℤ) :
    1/(q.den:ℝ) ≤ |(k:ℝ)*q-m| := by
  have hn : (k:ℤ)*q.num-m*q.den ≠ 0 := by
    intro he
    have hd : (q.den:ℤ) ∣ (k:ℤ)*q.num := by
      rw [sub_eq_zero.mp he]
      exact dvd_mul_left _ _
    have hdk : (q.den:ℤ) ∣ (k:ℤ) :=
      q.isCoprime_num_den.symm.dvd_of_dvd_mul_right hd
    exact hk (by exact_mod_cast hdk)
  have hnum : (1:ℝ) ≤ |(k:ℝ)*q.num-m*q.den| := by
    exact_mod_cast Int.one_le_abs hn
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hid : (k:ℝ)*q-m = ((k:ℝ)*q.num-m*q.den)/q.den := by
    rw [Rat.cast_def]
    field_simp
  rw [hid, abs_div, abs_of_pos hb]
  exact div_le_div_of_nonneg_right hnum hb.le

theorem nonresonant_distance (ξ : ℝ) (Q : ℕ) (q : ℚ) (h : Near ξ Q q)
    (k : ℕ) (hk : ¬ q.den ∣ k) (m : ℤ) :
    1/(q.den:ℝ)-k/((q.den:ℝ)*Q) ≤ |(k:ℝ)*ξ-m| := by
  exact (sub_le_sub_right (rational_nonresonant q k hk m) _).trans
    (integer_distance_lower ξ Q q h k m)

def residue (q : ℚ) (k : ℕ) : ℝ :=
  (q.den:ℝ)*|(k:ℝ)*q-round ((k:ℝ)*q)|

theorem residue_eq_integer (q : ℚ) (k : ℕ) :
    residue q k = |(((k:ℤ)*q.num-round ((k:ℝ)*q)*q.den:ℤ):ℝ)| := by
  unfold residue
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  rw [← abs_of_pos hb, ← abs_mul]
  congr 1
  push_cast
  rw [Rat.cast_def]
  field_simp

theorem residue_minimal (q : ℚ) (k : ℕ) (m : ℤ) :
    residue q k/(q.den:ℝ) ≤ |(k:ℝ)*q-m| := by
  unfold residue
  rw [mul_div_cancel_left₀ _ (by exact_mod_cast q.den_nz)]
  exact round_le _ _

theorem residue_ge_one (q : ℚ) (k : ℕ) (hk : ¬ q.den ∣ k) :
    1 ≤ residue q k := by
  have h := rational_nonresonant q k hk (round ((k:ℝ)*q))
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hh := (div_le_iff₀ hb).mp h
  unfold residue
  nlinarith

/-- Preserve the actual residue and the individual frequency, before rearrangement. -/
theorem residue_distance_lower (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : Near ξ Q q) (k : ℕ) (m : ℤ) :
    (residue q k-(k:ℝ)/Q)/(q.den:ℝ) ≤ |(k:ℝ)*ξ-m| := by
  have hh := (sub_le_sub_right (residue_minimal q k m)
    ((k:ℝ)/((q.den:ℝ)*Q))).trans (integer_distance_lower ξ Q q h k m)
  have hb : (q.den:ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have hQ' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hid : (residue q k-(k:ℝ)/Q)/(q.den:ℝ) =
      residue q k/q.den-(k:ℝ)/((q.den:ℝ)*Q) := by
    field_simp
  rw [hid]
  exact hh

theorem nonresonant_avoids_integers (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : Near ξ Q q) (k : ℕ) (hk : ¬ q.den ∣ k) (hkQ : k < Q)
    (m : ℤ) : (k:ℝ)*ξ ≠ m := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hf : (k:ℝ)/Q < 1 := (div_lt_one hQ').mpr (by exact_mod_cast hkQ)
  have hp : 0 < (residue q k-(k:ℝ)/Q)/(q.den:ℝ) :=
    div_pos (by linarith [residue_ge_one q k hk]) hb
  exact sub_ne_zero.mp (abs_pos.mp
    (hp.trans_le (residue_distance_lower ξ Q hQ q h k m)))

end
end Borwein.DirichletCover

