import Borwein.ResonantLimitPolynomial

set_option autoImplicit false

namespace Borwein.NonresonantGeometricBound
noncomputable section
open Complex AngularKernel ResonantGeometricSum FiniteBlockLocalization ZeroPoleBudget

theorem geometric_identity (M : ℕ) (z : ℂ) :
    (1-z)*geometricSum M z = z*(1-z^M) := by
  induction M with
  | zero => simp [geometricSum]
  | succ M ih =>
    have he : geometricSum (M+1) z = geometricSum M z+z^(M+1) := by
      simp [geometricSum,Finset.sum_range_succ]
    rw [he,mul_add,ih,pow_succ]
    ring

/-- The radial factor is retained; the unit-circle denominator cannot be used unchanged. -/
theorem radial_lower (ρ u : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    2*ρ*|Real.sin (u/2)| ≤ ‖1-(ρ:ℂ)*circle u‖ := by
  have he := radial_distance_sq ρ u
  have ha := sq_abs (Real.sin (u/2))
  have hm : 0 ≤ 4*ρ*(1-ρ)*(Real.sin (u/2))^2 := by positivity
  have hl : 0 ≤ 2*ρ*|Real.sin (u/2)| := by positivity
  nlinarith [sq_nonneg (1-ρ),norm_nonneg (1-(ρ:ℂ)*circle u)]

theorem geometric_bound (M : ℕ) (ρ u : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hu : 0 < |Real.sin (u/2)|) :
    ‖geometricSum M ((ρ:ℂ)*circle u)‖ ≤ 1/|Real.sin (u/2)| := by
  let z : ℂ := (ρ:ℂ)*circle u
  have hz : ‖z‖ = ρ := by simp [z,Real.norm_of_nonneg hρ.le,circle_norm]
  have hp : ‖1-z^M‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) (z^M)
    rw [norm_one,norm_pow,hz] at h
    have hpow : ρ^M ≤ 1 := pow_le_one₀ hρ.le hρ1
    linarith
  have hi := congrArg norm (geometric_identity M z)
  simp only [norm_mul,hz] at hi
  have hl := mul_le_mul_of_nonneg_right (radial_lower ρ u hρ.le hρ1)
    (norm_nonneg (geometricSum M z))
  change 2*ρ*|Real.sin (u/2)| * ‖geometricSum M z‖ ≤ ‖1-z‖*‖geometricSum M z‖ at hl
  rw [hi] at hl
  apply (le_div_iff₀ hu).mpr
  have hm := mul_le_mul_of_nonneg_left hp hρ.le
  nlinarith

theorem uniform_sine_lower (Q K k : ℕ) (θ : ℝ) (q : ℚ)
    (hQ : 0 < Q) (_hKQ : K < Q) (hkK : k ≤ K)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hk : ¬ q.den ∣ k) :
    2*(1-(K:ℝ)/Q)/(q.den:ℝ) ≤ |Real.sin ((k:ℝ)*θ/2)| := by
  have hs := residue_sine_lower (θ/(2*Real.pi)) Q hQ q hq k
  have he : Real.pi*((k:ℝ)*(θ/(2*Real.pi))) = (k:ℝ)*θ/2 := by field_simp
  rw [he] at hs
  apply le_trans _ hs
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q.den)
  have hk' : (k:ℝ)/Q ≤ (K:ℝ)/Q := div_le_div_of_nonneg_right (by exact_mod_cast hkK) (Nat.cast_nonneg Q)
  have hr := DirichletCover.residue_ge_one q k hk
  linarith

theorem point_geometric_bound (n M Q K k : ℕ) (τ θ : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hKQ : K < Q) (hkK : k ≤ K) (hτ : 0 ≤ τ)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hk : ¬ q.den ∣ k) :
    ‖geometricSum M ((point n τ θ)^k)‖ ≤ (q.den:ℝ)/(2*(1-(K:ℝ)/Q)) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have hs := uniform_sine_lower Q K k θ q hQ hKQ hkK hq hk
  have hpos : 0 < 2*(1-(K:ℝ)/Q)/(q.den:ℝ) := by positivity
  rw [point_pow]
  apply (geometric_bound M (Real.exp (-((k:ℝ)*τ/(5*n)))) ((k:ℝ)*θ)
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) (hpos.trans_le hs)).trans
  have h := one_div_le_one_div_of_le hpos hs
  convert h using 1 <;> field_simp

theorem denominator_five (n Q K : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hKQ : K < Q) (hτ : 0 ≤ τ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5) :
    ‖ResonantFourierSplit.nonresonant n K (point n τ θ) η q‖ ≤
      (5/(2*(1-(K:ℝ)/Q)))*Real.log (2/η) := by
  rw [ResonantFourierSplit.nonresonant_denominator_five n K (point n τ θ) η q hb]
  apply (norm_sum_le _ _).trans
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  calc
    _ ≤ ∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ 5 ∣ k),
        weight η k*(5/(2*(1-(K:ℝ)/Q))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hmem := Finset.mem_filter.mp hk
      have hw : 0 ≤ weight η k := by unfold weight; positivity
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw]
      apply mul_le_mul_of_nonneg_left _ hw
      have h := point_geometric_bound n (5*n) Q K k τ θ q hQ hKQ
        (Finset.mem_Icc.mp hmem.1).2 hτ hq (by simpa [hb] using hmem.2)
      simpa only [hb,Nat.cast_ofNat] using h
    _ = (5/(2*(1-(K:ℝ)/Q)))*∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ 5 ∣ k), weight η k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ResonantErrorBudget.weight_sum_bound _ η hη hη1) (by positivity)

theorem denominator_five_polynomial (n N Q K : ℕ) (τ θ : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 2 ≤ Q) (hKQ : K < Q)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : ResonantArgumentBounds.radiusBound N Q K (11/2) q < 2*Real.pi)
    (hb : q.den = 5) (hθ : OuterArcGeometry.region n (6/5) θ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp (n*(PhaseIntegral.radialR τ-(31:ℝ)/3125+2*(113/40000)+
        10*SmoothedLogTail.tail K (113/40000))+
        (5/(2*(1-(K:ℝ)/Q))+4*ExponentialKernelRemainder.kappa
          (ResonantArgumentBounds.radiusBound N Q K (11/2) q))*Real.log (2/(113/40000))) := by
  apply (ResonantLimitPolynomial.denominator_five_gap n N Q K τ θ q
    hN hn hQ hτ hT hq hZ hb hθ).trans
  apply Real.exp_le_exp.mpr
  have h := denominator_five n Q K τ θ (113/40000) q (by omega) hKQ hτ
    (by norm_num) (by norm_num) hq hb
  nlinarith

theorem denominator_five_decay (n N Q K : ℕ) (τ θ γ : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 2 ≤ Q) (hKQ : K < Q)
    (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : ResonantArgumentBounds.radiusBound N Q K (11/2) q < 2*Real.pi)
    (hb : q.den = 5) (hθ : OuterArcGeometry.region n (6/5) θ)
    (hbudget : 2*(113/40000)+10*SmoothedLogTail.tail K (113/40000)+
      (5/(2*(1-(K:ℝ)/Q))+4*ExponentialKernelRemainder.kappa
        (ResonantArgumentBounds.radiusBound N Q K (11/2) q))*Real.log (2/(113/40000))/(n:ℝ)
          ≤ (31:ℝ)/3125-γ) :
    ‖Polynomial.eval₂ (Int.castRingHom ℂ) (point n τ θ) (Borwein.polynomial n)‖ ≤
      Real.exp ((n:ℝ)*(PhaseIntegral.radialR τ-γ)) := by
  apply (denominator_five_polynomial n N Q K τ θ q hN hn hQ hKQ hτ hT hq hZ hb hθ).trans
  apply Real.exp_le_exp.mpr
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := (div_le_iff₀ hn0).mp (show
    (5/(2*(1-(K:ℝ)/Q))+4*ExponentialKernelRemainder.kappa
      (ResonantArgumentBounds.radiusBound N Q K (11/2) q))*Real.log (2/(113/40000))/(n:ℝ) ≤
        (31:ℝ)/3125-γ-2*(113/40000)-10*SmoothedLogTail.tail K (113/40000) by linarith)
  nlinarith

end
end Borwein.NonresonantGeometricBound
