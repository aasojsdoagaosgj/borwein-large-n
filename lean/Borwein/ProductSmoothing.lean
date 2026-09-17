import Borwein.Reciprocity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Borwein.ProductSmoothing
noncomputable section
open scoped BigOperators

theorem square_contraction (z : ℂ) (hz : ‖z‖ ≤ 1) (s : ℝ) (hs1 : s ≤ 1) :
    s*‖1-z‖^2 ≤ ‖1-(s:ℂ)*z‖^2 := by
  have hn : ‖z‖^2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hh := mul_nonneg (sub_nonneg.mpr hs1)
    (show 0 ≤ 1-s*‖z‖^2 by nlinarith [sq_nonneg ‖z‖])
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero] at hh ⊢
  nlinarith

theorem factor_smoothing (z : ℂ) (hz : ‖z‖ ≤ 1) (η : ℝ) (hη : 0 ≤ η) :
    ‖1-z‖ ≤ Real.exp (η/2)*‖1-(Real.exp (-η):ℂ)*z‖ := by
  have h := square_contraction z hz (Real.exp (-η))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hη))
  have he : Real.exp (-η/2)^2 = Real.exp (-η) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hh : Real.exp (-η/2)*‖1-z‖ ≤ ‖1-(Real.exp (-η):ℂ)*z‖ := by
    nlinarith [sq_nonneg (Real.exp (-η/2)*‖1-z‖-‖1-(Real.exp (-η):ℂ)*z‖),
      norm_nonneg (1-(Real.exp (-η):ℂ)*z), norm_nonneg (1-z), Real.exp_pos (-η/2)]
  have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (η/2)).le
  have hc : Real.exp (η/2)*Real.exp (-η/2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
  simpa only [← mul_assoc, hc, one_mul] using hm

theorem smoothed_factor_ne_zero (z : ℂ) (hz : ‖z‖ ≤ 1) (η : ℝ) (hη : 0 < η) :
    1-(Real.exp (-η):ℂ)*z ≠ 0 := by
  have he : Real.exp (-η) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hη)
  have hn : ‖(Real.exp (-η):ℂ)*z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (Real.exp_pos _).le hz) he
  intro h
  have hh : (Real.exp (-η):ℂ)*z = 1 := (sub_eq_zero.mp h).symm
  rw [hh, norm_one] at hn
  exact (lt_irrefl _ hn)

theorem finite_product_smoothing {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (η : ℝ) (hη : 0 ≤ η) :
    ‖∏ i ∈ s, (1-f i)‖ ≤ Real.exp ((s.card:ℝ)*η/2)*
      ‖∏ i ∈ s, (1-(Real.exp (-η):ℂ)*f i)‖ := by
  rw [norm_prod, norm_prod]
  have h := Finset.prod_le_prod (fun i _ => norm_nonneg (1-f i))
    (fun i hi => factor_smoothing (f i) (hf i hi) η hη)
  rw [Finset.prod_mul_distrib, Finset.prod_const] at h
  have he : Real.exp (η/2)^s.card = Real.exp ((s.card:ℝ)*η/2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simpa only [he] using h

def value (n : ℕ) (z : ℂ) := ∏ i : Fin n, ∏ a : Fin 4, (1-z^Borwein.exponent i a)
def smoothedValue (n : ℕ) (z : ℂ) (η : ℝ) :=
  ∏ i : Fin n, ∏ a : Fin 4, (1-(Real.exp (-η):ℂ)*z^Borwein.exponent i a)

theorem borwein_smoothing (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (η : ℝ) (hη : 0 ≤ η) :
    ‖value n z‖ ≤ Real.exp (2*η*n)*‖smoothedValue n z η‖ := by
  have h := finite_product_smoothing (Finset.univ : Finset (Fin n × Fin 4))
    (fun p => z^Borwein.exponent p.1 p.2) (by
      intro p _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg z) hz) η hη
  have he : ((Fintype.card (Fin n × Fin 4):ℝ)*η/2) = 2*η*n := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    ring
  simpa only [Finset.card_univ, he, Fintype.prod_prod_type, value, smoothedValue] using h


theorem value_eq_polynomial_eval (n : ℕ) (z : ℂ) :
    value n z = Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n) := by
  simp only [value, Borwein.polynomial, Borwein.block, Polynomial.eval₂_finsetProd,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_pow,
    Polynomial.eval₂_X]
  exact Fin.prod_univ_eq_prod_range
    (fun i : ℕ => ∏ a : Fin 4, (1-z^Borwein.exponent i a)) n

theorem smoothedValue_ne_zero (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (η : ℝ) (hη : 0 < η) :
    smoothedValue n z η ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro a _
  apply smoothed_factor_ne_zero _ _ η hη
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg z) hz

theorem factor_fourier (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun l : ℕ => (w^l/(l:ℂ)).re) (-Real.log ‖1-w‖) := by
  simpa only [Complex.neg_re, Complex.log_re] using
    Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hw)

theorem log_borwein_smoothing (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) (η : ℝ) (hη : 0 < η)
    (hv : value n z ≠ 0) :
    Real.log ‖value n z‖ ≤ 2*η*n+Real.log ‖smoothedValue n z η‖ := by
  have h := Real.log_le_log (norm_pos_iff.mpr hv) (borwein_smoothing n z hz η hη.le)
  rw [Real.log_mul (ne_of_gt (Real.exp_pos _))
    (norm_ne_zero_iff.mpr (smoothedValue_ne_zero n z hz η hη)), Real.log_exp] at h
  exact h

theorem finite_product_fourier {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (hw : ∀ i ∈ s, ‖w i‖ < 1) :
    HasSum (fun l : ℕ => ∑ i ∈ s, (w i ^ l / (l:ℂ)).re)
      (-Real.log ‖∏ i ∈ s, (1-w i)‖) := by
  have hn : ∀ i ∈ s, ‖1-w i‖ ≠ 0 := by
    intro i hi
    apply norm_ne_zero_iff.mpr
    intro h
    have hwi : w i = 1 := (sub_eq_zero.mp h).symm
    have hh := hw i hi
    simp [hwi] at hh
  have h := hasSum_sum (fun i hi => factor_fourier (w i) (hw i hi))
  rw [norm_prod, Real.log_prod hn]
  simpa only [Finset.sum_neg_distrib] using h

theorem smoothedValue_fourier (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    HasSum (fun l : ℕ => ∑ i : Fin n, ∑ a : Fin 4,
      (((Real.exp (-η):ℂ)*z^Borwein.exponent i a)^l/(l:ℂ)).re)
      (-Real.log ‖smoothedValue n z η‖) := by
  have h := finite_product_fourier (Finset.univ : Finset (Fin n × Fin 4))
    (fun p => (Real.exp (-η):ℂ)*z^Borwein.exponent p.1 p.2) (by
      intro p _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, norm_pow]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (Real.exp_pos _).le
        (pow_le_one₀ (norm_nonneg z) hz))
        (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hη)))
  simpa only [Fintype.sum_prod_type, Fintype.prod_prod_type, smoothedValue] using h

theorem polynomial_log_fourier_upper (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (η : ℝ) (hη : 0 < η)
    (hv : Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n) ≠ 0) :
    Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n)‖ ≤
      2*η*n - ∑' l : ℕ, ∑ i : Fin n, ∑ a : Fin 4,
        (((Real.exp (-η):ℂ)*z^Borwein.exponent i a)^l/(l:ℂ)).re := by
  have hv' : value n z ≠ 0 := by rwa [value_eq_polynomial_eval]
  have h := log_borwein_smoothing n z hz η hη hv'
  rw [value_eq_polynomial_eval] at h
  rw [(smoothedValue_fourier n z hz η hη).tsum_eq]
  simpa only [sub_neg_eq_add] using h

end
end Borwein.ProductSmoothing
