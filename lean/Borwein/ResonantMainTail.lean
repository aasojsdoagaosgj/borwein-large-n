import Borwein.SmoothedResonantMain
import Borwein.SmoothedLogTail

set_option autoImplicit false

namespace Borwein.ResonantMainTail
noncomputable section
open Complex MeasureTheory SmoothedLogTail SmoothedResonantMain ResonantArgumentBounds

def limit (b c : ℕ) (η : ℝ) (z : ℂ) : ℂ :=
  5*integral b η z-integral c η z

def height (b c : ℕ) (η : ℝ) (z : ℂ) : ℝ := -(limit b c η z).re

theorem main_eq_partial (n K c : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hc : ∀ k : ℕ, q.den ∣ 5*k ↔ c ∣ k) :
    ResonantFourierSplit.main n K τ θ η q =
      (n:ℂ)*(5*partialSum q.den K η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)-
        partialSum c K η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)) := by
  unfold ResonantFourierSplit.main partialSum argument
  simp only [hc,neg_mul]
  rw [mul_sub,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro k _ <;> ring

theorem limit_error (b c K : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hc : 0 < c) (hη : 0 < η) (hz : 0 ≤ z.re) :
    ‖(5*partialSum b K η z-partialSum c K η z)-limit b c η z‖ ≤ 6*tail K η := by
  have h1 := truncation_bound b K η z hb hη hz
  have h2 := truncation_bound c K η z hc hη hz
  have he : (5*partialSum b K η z-partialSum c K η z)-limit b c η z =
      5*(partialSum b K η z-integral b η z)-(partialSum c K η z-integral c η z) := by
    unfold limit
    ring
  rw [he]
  have h := norm_sub_le (5*(partialSum b K η z-integral b η z))
    (partialSum c K η z-integral c η z)
  norm_num only [norm_mul,Complex.norm_ofNat] at h
  change ‖partialSum b K η z-integral b η z‖ ≤ tail K η at h1
  change ‖partialSum c K η z-integral c η z‖ ≤ tail K η at h2
  linarith

theorem main_error (n K c : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hc : 0 < c) (hd : ∀ k : ℕ, q.den ∣ 5*k ↔ c ∣ k)
    (hη : 0 < η) (hτ : 0 ≤ τ) :
    ‖ResonantFourierSplit.main n K τ θ η q-
      (n:ℂ)*limit q.den c η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)‖ ≤
        6*n*tail K η := by
  rw [main_eq_partial n K c τ θ η q hd,← mul_sub,norm_mul,Complex.norm_natCast]
  have h := mul_le_mul_of_nonneg_left
    (limit_error q.den c K η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)
      q.pos hc hη (by simpa using hτ)) (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  exact h.trans_eq (by ring)

theorem main_real_upper (n K c : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hc : 0 < c) (hd : ∀ k : ℕ, q.den ∣ 5*k ↔ c ∣ k)
    (hη : 0 < η) (hτ : 0 ≤ τ) :
    -(ResonantFourierSplit.main n K τ θ η q).re ≤
      n*height q.den c η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)+6*n*tail K η := by
  have he := main_error n K c τ θ η q hc hd hη hτ
  have hr := Complex.re_le_norm (-(ResonantFourierSplit.main n K τ θ η q-
      (n:ℂ)*limit q.den c η ((τ:ℂ)-(DirichletCover.localAngle n θ q:ℂ)*I)))
  simp only [norm_neg,Complex.neg_re,Complex.sub_re,Complex.mul_re,
    Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hr
  unfold height
  linarith

theorem coprime_filter (b : ℕ) (hb : b.Coprime 5) (k : ℕ) :
    b ∣ 5*k ↔ b ∣ k := hb.dvd_mul_left

theorem five_filter (B k : ℕ) : 5*B ∣ 5*k ↔ B ∣ k :=
  Nat.mul_dvd_mul_iff_left (by norm_num)

theorem coprime_height (b : ℕ) (η : ℝ) (z : ℂ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) :
    height b b η z = (4/(b:ℝ))*poleIntegral b η z := by
  have he : limit b b η z = 4*integral b η z := by unfold limit; ring
  rw [height,he,coprime_main b η z hb hη hz]

theorem five_height (B : ℕ) (η τ t : ℝ)
    (hB : 0 < B) (hη : 0 < η) (hτ : 0 ≤ τ) :
    height (5*B) B η ((τ:ℂ)-(t:ℂ)*I) =
      SmoothedPhase.smoothedModulus ((B:ℝ)*η) ((B:ℝ)*τ) ((B:ℝ)*t)/(B:ℝ) :=
  five_smoothed_modulus B η τ t hB hη hτ

end
end Borwein.ResonantMainTail
