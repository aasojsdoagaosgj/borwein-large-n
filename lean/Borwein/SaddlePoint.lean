import Borwein.RadialDerivatives

/-! Decay of -R' and existence and uniqueness of the positive real saddle. -/

namespace Borwein.SaddlePoint
noncomputable section
open scoped BigOperators Topology
open Borwein.PhaseGap Borwein.PhaseIntegral Borwein.RadialMoments
open Borwein.RadialDerivatives Filter

theorem moment_zero_ge_one (y : ℝ) : 1 ≤ moment 0 y := by
  have h := Finset.single_le_sum
    (fun (j : Fin 5) _ => (Real.exp_pos (-(j : ℝ)*y)).le) (Finset.mem_univ (0 : Fin 5))
  simpa [moment_zero, radialSum] using h

theorem mean_le_ten_exp_neg (y : ℝ) (hy : 0 ≤ y) : mean y ≤ 10*Real.exp (-y) := by
  have hm : 0 ≤ moment 1 y := by
    unfold moment
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (by positivity) (Real.exp_pos _).le
  calc
    mean y = moment 1 y / moment 0 y := rfl
    _ ≤ moment 1 y := div_le_self hm (moment_zero_ge_one y)
    _ ≤ ∑ j : Fin 5, (j : ℝ)*Real.exp (-y) := by
      unfold moment
      simp only [pow_one]
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j = 0
      · subst j; simp
      have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
        have hn : 0 < (j : ℕ) := Nat.pos_of_ne_zero (by
          intro hzero
          apply hj
          exact Fin.ext hzero)
        exact_mod_cast hn
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = 10*Real.exp (-y) := by rw [← Finset.sum_mul]; norm_num [Fin.sum_univ_five]

theorem firstDerivative_neg (τ : ℝ) : firstDerivative τ < 0 := by
  have hc : Continuous (fun x : ℝ => x * mean (τ*x)) := by fun_prop
  have hp : 0 < ∫ x in (0 : ℝ)..1, x * mean (τ*x) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable 0 1) _ (by norm_num)
    intro x hx
    exact mul_pos hx.1 (mean_pos _)
  have he : firstDerivative τ = -(∫ x in (0 : ℝ)..1, x * mean (τ*x)) := by
    simp [firstDerivative, firstDensity, neg_mul, intervalIntegral.integral_neg]
  linarith

theorem neg_firstDerivative_le (τ : ℝ) (hτ : 0 < τ) : -firstDerivative τ ≤ 10/τ := by
  have hc : Continuous (fun x : ℝ => x * mean (τ*x)) := by fun_prop
  have hec : Continuous (fun x : ℝ => 10*Real.exp (-τ*x)) := by fun_prop
  have hexp : (∫ x in (0 : ℝ)..1, Real.exp (-τ*x)) = (Real.exp (-τ)-1)/(-τ) := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr (ne_of_gt hτ))]
    simp [integral_exp, div_eq_mul_inv]
    ring
  calc
    -firstDerivative τ = ∫ x in (0 : ℝ)..1, x * mean (τ*x) := by
      simp [firstDerivative, firstDensity, neg_mul, intervalIntegral.integral_neg]
    _ ≤ ∫ x in (0 : ℝ)..1, 10*Real.exp (-τ*x) := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hc.intervalIntegrable 0 1)
        (hec.intervalIntegrable 0 1)
      intro x hx
      have hm := mean_le_ten_exp_neg (τ*x) (mul_nonneg hτ.le hx.1)
      calc
        x * mean (τ*x) ≤ mean (τ*x) := mul_le_of_le_one_left (mean_nonneg _) hx.2
        _ ≤ 10*Real.exp (-τ*x) := by simpa [neg_mul] using hm
    _ = 10*(1-Real.exp (-τ))/τ := by
      rw [intervalIntegral.integral_const_mul, hexp]
      ring
    _ ≤ 10/τ := by
      apply div_le_div_of_nonneg_right _ hτ.le
      nlinarith [Real.exp_pos (-τ)]

theorem tendsto_firstDerivative_atTop : Tendsto firstDerivative atTop (𝓝 0) := by
  have hlim : Tendsto (fun τ : ℝ => 10/τ) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using tendsto_inv_atTop_zero.const_mul (10 : ℝ)
  have hb : ∀ᶠ τ : ℝ in atTop, -firstDerivative τ ≤ 10/τ :=
    (eventually_gt_atTop 0).mono (fun τ hτ => neg_firstDerivative_le τ hτ)
  have hnonneg : ∀ᶠ τ : ℝ in atTop, 0 ≤ -firstDerivative τ :=
    Eventually.of_forall (fun τ => neg_nonneg.mpr (firstDerivative_neg τ).le)
  have h := squeeze_zero' hnonneg hb hlim
  simpa using h.neg

theorem continuous_firstDerivative : Continuous firstDerivative :=
  continuous_iff_continuousAt.mpr (fun τ => (hasDerivAt_firstDerivative τ).continuousAt)

/-- Every ratio in (0,1) has a unique positive saddle, in the original derivative equation. -/
theorem existsUnique_positive_saddle (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) :
    ∃! τ : ℝ, 0 < τ ∧ -deriv radialR τ = r := by
  have hlarge : ∀ᶠ τ : ℝ in atTop, -r < firstDerivative τ :=
    tendsto_firstDerivative_atTop.eventually (eventually_gt_nhds (by linarith : -r < 0))
  obtain ⟨T, hT0, hT⟩ := ((eventually_gt_atTop (0 : ℝ)).and hlarge).exists
  have hiv := intermediate_value_Icc hT0.le continuous_firstDerivative.continuousOn
  obtain ⟨τ, hτ, hvalue⟩ := hiv (show -r ∈ Set.Icc (firstDerivative 0) (firstDerivative T) from
    ⟨by rw [firstDerivative_zero]; linarith, hT.le⟩)
  have hτ0 : 0 < τ := by
    rcases eq_or_lt_of_le hτ.1 with he | hp
    · subst τ; rw [firstDerivative_zero] at hvalue; linarith
    · exact hp
  refine ⟨τ, ⟨hτ0, ?_⟩, ?_⟩
  · rw [deriv_radialR, hvalue]; ring
  · intro u hu
    apply strictMono_firstDerivative.injective
    rw [hvalue]
    rw [deriv_radialR] at hu
    linarith [hu.2]

theorem existsUnique_saddle_index (n k : ℕ) (hn : 0 < n) (hk0 : 0 < k) (hk : k < 5*n^2) :
    ∃! τ : ℝ, 0 < τ ∧ -deriv radialR τ = (k : ℝ)/(5*(n : ℝ)^2) := by
  apply existsUnique_positive_saddle
  · apply div_pos
    · exact_mod_cast hk0
    · positivity
  · apply (div_lt_one (by positivity : 0 < 5*(n : ℝ)^2)).mpr
    exact_mod_cast hk

theorem saddle_center : -deriv radialR 0 = 1 := by
  rw [deriv_radialR, firstDerivative_zero]
  norm_num

theorem saddle_center_unique (τ : ℝ) (hτ : -deriv radialR τ = 1) : τ = 0 := by
  apply strictMono_firstDerivative.injective
  rw [firstDerivative_zero]
  rw [deriv_radialR] at hτ
  linarith

theorem strictAnti_radialR : StrictAnti radialR := by
  apply strictAnti_of_deriv_neg
  intro τ
  rw [deriv_radialR]
  exact firstDerivative_neg τ

end
end Borwein.SaddlePoint
