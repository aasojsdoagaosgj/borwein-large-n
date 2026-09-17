import Borwein.ResonantErrorBudget

namespace Borwein.ResonantArgumentBounds
noncomputable section
open Complex MeasureTheory DirichletCover ExponentialKernelRemainder ResonantErrorBudget ZeroPoleBudget

def argument (n : ℕ) (τ θ : ℝ) (q : ℚ) (k : ℕ) : ℂ :=
  (k:ℂ)*((τ:ℂ)-(localAngle n θ q:ℂ)*I)

def radiusBound (N Q K : ℕ) (T : ℝ) (q : ℚ) : ℝ :=
  T*(K:ℝ)/(N:ℝ)+10*Real.pi*K/((q.den:ℝ)*Q)

theorem phase_norm (τ t : ℝ) (hτ : 0 ≤ τ) : ‖(τ:ℂ)-(t:ℂ)*I‖ ≤ τ+|t| := by
  have h := norm_sub_le (τ:ℂ) ((t:ℂ)*I)
  simpa [norm_mul,Real.norm_of_nonneg hτ] using h

theorem argument_norm (n M k : ℕ) (τ θ : ℝ) (q : ℚ) (hτ : 0 ≤ τ) :
    ‖argument n τ θ q k/(M:ℂ)‖ ≤ (k:ℝ)*(τ+|localAngle n θ q|)/(M:ℝ) := by
  rw [argument,norm_div,norm_mul,Complex.norm_natCast,Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (phase_norm τ _ hτ) (Nat.cast_nonneg k))
    (Nat.cast_nonneg M)

theorem argument_upper (n N M Q K k : ℕ) (τ T θ : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hM : n ≤ M) (hQ : 0 < Q) (hk : k ≤ K)
    (hτ : 0 ≤ τ) (hT : τ ≤ T) (hq : Near (θ/(2*Real.pi)) Q q) :
    ‖argument n τ θ q k/(M:ℂ)‖ ≤ radiusBound N Q K T q := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  have hT0 : 0 ≤ T := hτ.trans hT
  have ht := localAngle_bound n Q θ q hq
  have hb := argument_norm n M k τ θ q hτ
  have hden := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ (k:ℝ)*(τ+|localAngle n θ q|)) hn0
    (show (n:ℝ) ≤ (M:ℝ) by exact_mod_cast hM)
  have hnum := div_le_div_of_nonneg_right
    (mul_le_mul (by exact_mod_cast hk : (k:ℝ) ≤ K) (add_le_add hT ht)
      (by positivity : 0 ≤ τ+|localAngle n θ q|) (Nat.cast_nonneg K)) hn0.le
  have he : (K:ℝ)*(T+10*Real.pi*n/((q.den:ℝ)*Q))/(n:ℝ) =
      T*K/(n:ℝ)+10*Real.pi*K/((q.den:ℝ)*Q) := by field_simp
  rw [he] at hnum
  have hm := div_le_div_of_nonneg_left (mul_nonneg hT0 (Nat.cast_nonneg K)) hN0
    (show (N:ℝ) ≤ (n:ℝ) by exact_mod_cast hn)
  unfold radiusBound
  exact (hb.trans (hden.trans hnum)).trans (add_le_add hm le_rfl)

theorem actual_resonant_error (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) :
    ‖(∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ k),
        (weight η k:ℂ)*error (5*n) (argument n τ θ q k))-
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ 5*k),
        (weight η k:ℂ)*error n (argument n τ θ q k))‖/(n:ℝ) ≤
      4*kappa (radiusBound N Q K T q)*Real.log (2/η)/(n:ℝ) := by
  have hT0 : 0 ≤ T := hτ.trans hT
  apply two_sums_bound _ _ n (argument n τ θ q) η (radiusBound N Q K T q)
    (by omega) hη hη1 (by unfold radiusBound; positivity) hZ
  · intro k _
    simp only [argument,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
      Complex.natCast_re,Complex.natCast_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero]
    positivity
  · intro k hk
    have hkK : k ≤ K := by
      rcases Finset.mem_union.mp hk with hk | hk
      all_goals exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
    exact argument_upper n N n Q K k τ T θ q hN hn le_rfl hQ hkK hτ hT hq

end
end Borwein.ResonantArgumentBounds
