import Borwein.ProductSmoothing
import Mathlib.Algebra.Field.GeomSum

namespace Borwein.FiniteFourierKernel
noncomputable section
open scoped BigOperators

def finiteSum (n : ℕ) (z : ℂ) :=
  ∑ i : Fin n, ∑ a : Fin 4, z^Borwein.exponent i a

def kernel (z : ℂ) := z*(1-z^4)/((1-z)*(1-z^5))

theorem finiteSum_blocks (n : ℕ) (z : ℂ) :
    finiteSum n z = (∑ i ∈ Finset.range n, (z^5)^i)*(z+z^2+z^3+z^4) := by
  unfold finiteSum
  rw [Finset.sum_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero,
    Borwein.exponent]
  simp only [pow_add, pow_mul, pow_one, pow_zero]
  ring

theorem exact_block (n : ℕ) (z : ℂ) (hz : z ≠ 1) (hz5 : z^5 ≠ 1) :
    finiteSum n z = (1-z^(5*n))*kernel z := by
  rw [finiteSum_blocks, geom_sum_eq hz5]
  unfold kernel
  rw [pow_mul]
  have h1 : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h5 : 1-z^5 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz5)
  have h5' : z^5-1 ≠ 0 := sub_ne_zero.mpr hz5
  field_simp
  ring

theorem norm_exact_block (n : ℕ) (z : ℂ) (hz : z ≠ 1) (hz5 : z^5 ≠ 1) :
    ‖finiteSum n z‖ ≤ (1+‖z‖^(5*n))*‖kernel z‖ := by
  rw [exact_block n z hz hz5, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [norm_one, norm_pow] using norm_sub_le (1:ℂ) (z^(5*n))

theorem fourier_term (n l : ℕ) (z : ℂ) (η : ℝ) :
    (∑ i : Fin n, ∑ a : Fin 4,
      (((Real.exp (-η):ℂ)*z^Borwein.exponent i a)^l/(l:ℂ)).re) =
      (((Real.exp (-η):ℂ)^l/(l:ℂ))*finiteSum n (z^l)).re := by
  simp only [finiteSum, Finset.mul_sum, mul_pow, div_eq_mul_inv,
    Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [← pow_mul, ← pow_mul, Nat.mul_comm (Borwein.exponent i a) l]
  congr 1
  ring

theorem smoothed_fourier (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (η : ℝ) (hη : 0 < η) :
    HasSum (fun l : ℕ => (((Real.exp (-η):ℂ)^l/(l:ℂ))*finiteSum n (z^l)).re)
      (-Real.log ‖ProductSmoothing.smoothedValue n z η‖) := by
  exact (ProductSmoothing.smoothedValue_fourier n z hz η hη).congr_fun
    (fun l => (fourier_term n l z η).symm)

theorem finiteSum_norm_le (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖finiteSum n z‖ ≤ 4*(n:ℝ) := by
  unfold finiteSum
  calc
    ‖∑ i : Fin n, ∑ a : Fin 4, z^Borwein.exponent i a‖ ≤
        ∑ i : Fin n, ∑ a : Fin 4, ‖z^Borwein.exponent i a‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i : Fin n, ∑ a : Fin 4, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro a _
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg z) hz
    _ = 4*(n:ℝ) := by simp; ring

def coefficient (n l : ℕ) (z : ℂ) (r : ℝ) :=
  ((r:ℂ)^l/(l:ℂ))*finiteSum n (z^l)

theorem coefficient_exact_block (n l : ℕ) (z : ℂ) (r : ℝ)
    (hz : z^l ≠ 1) (hz5 : (z^l)^5 ≠ 1) :
    coefficient n l z r = ((r:ℂ)^l/(l:ℂ)) *
      ((1-(z^l)^(5*n))*kernel (z^l)) := by
  unfold coefficient
  rw [exact_block n (z^l) hz hz5]

theorem coefficient_norm_le (n l : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) :
    ‖coefficient n l z r‖ ≤ (r^l/(l:ℝ))*(4*n) := by
  unfold coefficient
  rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr,
    Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (pow_nonneg hr _) (Nat.cast_nonneg _))
  apply finiteSum_norm_le
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg z) hz

theorem tail_term_bound (n K j : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) :
    ‖coefficient n (j+(K+1)) z r‖ ≤
      (4*n*r^(K+1)/(K+1:ℕ))*r^j := by
  have hden : (0:ℝ) < (K+1:ℕ) := by positivity
  have hle : ((K+1:ℕ):ℝ) ≤ (j+(K+1):ℕ) := by exact_mod_cast Nat.le_add_left (K+1) j
  have h := div_le_div_of_nonneg_left (pow_nonneg hr (j+(K+1))) hden hle
  have hh := mul_le_mul_of_nonneg_right h (show (0:ℝ) ≤ 4*n by positivity)
  have hb := coefficient_norm_le n (j+(K+1)) z hz r hr
  refine hb.trans (hh.trans_eq ?_)
  rw [pow_add]
  ring

theorem fourier_tail_bound (n K : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖∑' j : ℕ, coefficient n (j+(K+1)) z r‖ ≤
      (4*n*r^(K+1)/(K+1:ℕ))*(1-r)⁻¹ := by
  apply tsum_of_norm_bounded
    ((hasSum_geometric_of_lt_one hr hr1).mul_left (4*n*r^(K+1)/(K+1:ℕ)))
  exact fun j => tail_term_bound n K j z hz r hr

theorem coefficient_summable (n : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun l : ℕ => coefficient n l z r) := by
  apply (summable_nat_add_iff 1).mp
  exact ((hasSum_geometric_of_lt_one hr hr1).mul_left
    (4*n*r^(0+1)/(0+1:ℕ))).summable.of_norm_bounded
    (fun j => tail_term_bound n 0 j z hz r hr)

theorem truncation_error (n K : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) :
    ‖(∑ l ∈ Finset.range (K+1), coefficient n l z r) -
      ∑' l : ℕ, coefficient n l z r‖ ≤
      (4*n*r^(K+1)/(K+1:ℕ))*(1-r)⁻¹ := by
  rw [← (coefficient_summable n z hz r hr hr1).sum_add_tsum_nat_add (K+1)]
  rw [sub_add_cancel_left, norm_neg]
  exact fourier_tail_bound n K z hz r hr hr1

theorem polynomial_log_truncated_upper (n K : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (η : ℝ) (hη : 0 < η)
    (hv : Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n) ≠ 0) :
    Real.log ‖Polynomial.eval₂ (Int.castRingHom ℂ) z (Borwein.polynomial n)‖ ≤
      2*η*n - (∑ l ∈ Finset.range (K+1), coefficient n l z (Real.exp (-η))).re +
      (4*n*(Real.exp (-η))^(K+1)/(K+1:ℕ))*(1-Real.exp (-η))⁻¹ := by
  have hr := (Real.exp_pos (-η)).le
  have hr1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hη)
  have hs := coefficient_summable n z hz (Real.exp (-η)) hr hr1
  have hf := (smoothed_fourier n z hz η hη).tsum_eq
  change (∑' l : ℕ, (coefficient n l z (Real.exp (-η))).re) = _ at hf
  rw [← Complex.re_tsum hs] at hf
  have he := (Complex.re_le_norm
    ((∑ l ∈ Finset.range (K+1), coefficient n l z (Real.exp (-η))) -
      ∑' l : ℕ, coefficient n l z (Real.exp (-η)))).trans
    (truncation_error n K z hz (Real.exp (-η)) hr hr1)
  rw [Complex.sub_re, hf] at he
  have hv' : ProductSmoothing.value n z ≠ 0 := by
    rwa [ProductSmoothing.value_eq_polynomial_eval]
  have h := ProductSmoothing.log_borwein_smoothing n z hz η hη hv'
  rw [ProductSmoothing.value_eq_polynomial_eval] at h
  linarith

end
end Borwein.FiniteFourierKernel
