import Borwein.EndpointTailFourier

set_option autoImplicit false

namespace Borwein.EndpointTailRootSeries
noncomputable section
open Complex EndpointTailLog EndpointTailFourier

def rootTerm (n : ℕ) (ξ w : ℂ) (l : ℕ) : ℂ :=
  (exp (-((5*n:ℕ):ℂ)*w))^(l+1)/((l+1:ℕ):ℂ)*
    (1/(ξ^(-((l+1:ℕ):ℤ))*exp (((l+1:ℕ):ℂ)*w)-1)-
      1/(exp (5*((l+1:ℕ):ℂ)*w)-1))

theorem factored_frequency (n l : ℕ) (q : ℂ) :
    frequency (5*n) q l-frequency n (q^5) l =
      (q^(5*n))^(l+1)/((l+1:ℕ):ℂ)*
        (q^(l+1)/(1-q^(l+1))-q^(5*(l+1))/(1-q^(5*(l+1)))) := by
  have h1 : q^((5*n+1)*(l+1)) = (q^(5*n))^(l+1)*q^(l+1) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  have h5 : (q^5)^((n+1)*(l+1)) = (q^(5*n))^(l+1)*q^(5*(l+1)) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  unfold frequency
  rw [h1, h5, ← pow_mul]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem ratio_inverse (u : ℂ) (hu : u ≠ 0) : u/(1-u) = 1/(u⁻¹-1) := by
  by_cases h1 : u=1
  · simp [h1]
  have hd : 1-u ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp

theorem root_power (ξ w : ℂ) (k : ℕ) :
    (ξ*exp (-w))^k = ξ^k*exp (-(k:ℂ)*w) := by
  rw [mul_pow, ← Complex.exp_nat_mul]
  congr 1
  congr 1
  ring

theorem fifth_power (ξ w : ℂ) (k : ℕ) (hξ : ξ^5=1) :
    (ξ*exp (-w))^(5*k) = exp (-((5*k:ℕ):ℂ)*w) := by
  rw [root_power, pow_mul, hξ, one_pow, one_mul]

theorem inverse_root_power (ξ w : ℂ) (k : ℕ) :
    ((ξ*exp (-w))^k)⁻¹ = ξ^(-(k:ℤ))*exp ((k:ℂ)*w) := by
  rw [root_power, mul_inv_rev, zpow_neg, zpow_natCast, ← Complex.exp_neg]
  have he : -(-(k:ℂ)*w) = (k:ℂ)*w := by ring
  rw [he, mul_comm]

theorem root_frequency (n l : ℕ) (ξ w : ℂ) (hξ : ξ^5=1) :
    frequency (5*n) (ξ*exp (-w)) l-frequency n ((ξ*exp (-w))^5) l = rootTerm n ξ w l := by
  have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
  have hq0 : ξ*exp (-w) ≠ 0 := mul_ne_zero hξ0 (Complex.exp_ne_zero _)
  rw [factored_frequency, fifth_power ξ w n hξ,
    ratio_inverse _ (pow_ne_zero _ hq0), ratio_inverse _ (pow_ne_zero _ hq0),
    inverse_root_power]
  have he : ((ξ*exp (-w))^(5*(l+1)))⁻¹ = exp (5*((l+1:ℕ):ℂ)*w) := by
    rw [fifth_power ξ w (l+1) hξ, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [he]
  rfl

/-- The exact endpoint tail series in manuscript §5.3, with the logarithm's branch fixed. -/
theorem tailLog_root_series (n : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hq : ‖ξ*exp (-w)‖ < 1) :
    tailLog n (ξ*exp (-w)) = ∑' l : ℕ, rootTerm n ξ w l := by
  rw [tailLog_series n _ hq]
  exact tsum_congr (fun l => root_frequency n l ξ w hξ)

theorem rootTerm_summable (n : ℕ) (ξ w : ℂ) (hξ : ξ^5=1)
    (hq : ‖ξ*exp (-w)‖ < 1) : Summable (rootTerm n ξ w) := by
  have hq5 : ‖(ξ*exp (-w))^5‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by norm_num)
  exact ((frequency_summable (5*n) _ hq).sub (frequency_summable n _ hq5)).congr
    (fun l => root_frequency n l ξ w hξ)

theorem actual_root_fifth (j : Fin 4) : (FivePoleCircle.zeta^(j.val+1))^5 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, FivePoleCircle.zeta_primitive.pow_eq_one, one_pow]

theorem four_root_series (n : ℕ) (j : Fin 4) (w : ℂ) (hw : 0 < w.re) :
    tailLog n (FivePoleCircle.zeta^(j.val+1)*exp (-w)) =
      ∑' l : ℕ, rootTerm n (FivePoleCircle.zeta^(j.val+1)) w l := by
  exact tailLog_root_series n _ w (actual_root_fifth j) (EndpointFiniteConnection.root_norm j w hw)

theorem polynomial_fourier_tail (n : ℕ) (j : Fin 4) (w : ℂ) (hw : 0 < w.re) :
    Polynomial.eval₂ (Int.castRingHom ℂ) (FivePoleCircle.zeta^(j.val+1)*exp (-w))
      (Borwein.polynomial n) =
        EndpointEta.G (FivePoleCircle.zeta^(j.val+1)*exp (-w))*
          exp (∑' l : ℕ, rootTerm n (FivePoleCircle.zeta^(j.val+1)) w l) := by
  rw [polynomial_eq_G_exp n _ (EndpointFiniteConnection.root_norm j w hw), four_root_series n j w hw]

end
end Borwein.EndpointTailRootSeries
