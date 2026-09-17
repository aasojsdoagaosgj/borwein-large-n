import Borwein.EndpointTailRootSeries

set_option autoImplicit false

namespace Borwein.EndpointTailGlobalKernel
noncomputable section
open Complex EndpointTailFourier

def kernel (z : ℂ) : ℂ := z/(1-z)-z^5/(1-z^5)
def term (n : ℕ) (q : ℂ) (l : ℕ) : ℂ := frequency (5*n) q l-frequency n (q^5) l

theorem kernel_polynomial (z : ℂ) (hz : ‖z‖ < 1) :
    kernel z = (z+z^2+z^3+z^4)/(1-z^5) := by
  have hz1 : z ≠ 1 := by intro he; simpa [he] using hz
  have hz5 : z^5 ≠ 1 := by
    intro he
    have hn : ‖z^5‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hz (by norm_num)
    simpa [he] using hn
  have h1 : 1-z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have h5 : 1-z^5 ≠ 0 := sub_ne_zero.mpr hz5.symm
  unfold kernel
  field_simp
  ring

theorem kernel_bound (z : ℂ) (hz : ‖z‖ < 1) : ‖kernel z‖ ≤ 4/(1-‖z‖^5) := by
  rw [kernel_polynomial z hz, norm_div]
  have hnum : ‖z+z^2+z^3+z^4‖ ≤ 4 := by
    have ha := norm_add_le (z+z^2+z^3) (z^4)
    have hb := norm_add_le (z+z^2) (z^3)
    have hc := norm_add_le z (z^2)
    simp only [Complex.norm_pow] at ha hb hc
    have h2 := pow_le_one₀ (norm_nonneg z) hz.le (n := 2)
    have h3 := pow_le_one₀ (norm_nonneg z) hz.le (n := 3)
    have h4 := pow_le_one₀ (norm_nonneg z) hz.le (n := 4)
    linarith
  have hp : 0 < 1-‖z‖^5 := sub_pos.mpr (pow_lt_one₀ (norm_nonneg z) hz (by norm_num))
  have hden : 1-‖z‖^5 ≤ ‖1-z^5‖ := by
    convert! (norm_sub_norm_le (1:ℂ) (z^5)) using 1 <;> simp
  exact div_le_div₀ (by norm_num) hnum hp hden

theorem frequency_kernel (n l : ℕ) (q : ℂ) :
    term n q l = (q^(5*n))^(l+1)/((l+1:ℕ):ℂ)*kernel (q^(l+1)) := by
  rw [term, EndpointTailRootSeries.factored_frequency]
  simp only [kernel, ← pow_mul, Nat.mul_comm (l+1) 5]

theorem power_kernel_bound (q : ℂ) (hq : ‖q‖ < 1) (l : ℕ) :
    ‖kernel (q^(l+1))‖ ≤ 4/(1-‖q‖^5) := by
  have hp : ‖q^(l+1)‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  have hb := kernel_bound _ hp
  rw [norm_pow, ← pow_mul] at hb
  have hpow : ‖q‖^((l+1)*5) ≤ ‖q‖^5 :=
    pow_le_pow_of_le_one (norm_nonneg _) hq.le (by omega)
  have hd : 0 < 1-‖q‖^5 := sub_pos.mpr (pow_lt_one₀ (norm_nonneg _) hq (by norm_num))
  exact hb.trans (div_le_div_of_nonneg_left (by norm_num) hd (by linarith))

theorem term_bound (n l : ℕ) (q : ℂ) (hq : ‖q‖ < 1) :
    ‖term n q l‖ ≤ (4/(1-‖q‖^5))*(‖q‖^(5*n))^(l+1) := by
  rw [frequency_kernel, norm_mul, norm_div, norm_pow, norm_pow, Complex.norm_natCast]
  have hfrac : (‖q‖^(5*n))^(l+1)/((l+1:ℕ):ℝ) ≤ (‖q‖^(5*n))^(l+1) :=
    div_le_self (by positivity) (by exact_mod_cast Nat.le_add_left 1 l)
  have hb := mul_le_mul hfrac (power_kernel_bound q hq l) (norm_nonneg _)
    (by positivity : 0 ≤ (‖q‖^(5*n))^(l+1))
  simpa only [mul_comm] using hb

end
end Borwein.EndpointTailGlobalKernel
