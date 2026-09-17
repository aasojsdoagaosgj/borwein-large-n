import Borwein.ResonantGeometricSum

set_option autoImplicit false

namespace Borwein.ResonantFourierSplit
noncomputable section
open Complex MeasureTheory FiniteBlockLocalization ZeroPoleBudget ResonantGeometricSum
  ResonantArgumentBounds ExponentialKernelRemainder

def full (n K : ℕ) (z : ℂ) (η : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, (weight η k:ℂ)*FiniteFourierKernel.finiteSum n (z^k)

def discrete (n K : ℕ) (z : ℂ) (η : ℝ) (q : ℚ) : ℂ :=
  (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ k),
    (weight η k:ℂ)*geometricSum (5*n) (z^k))-
  (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ 5*k),
    (weight η k:ℂ)*geometricSum n (z^(5*k)))

def nonresonant (n K : ℕ) (z : ℂ) (η : ℝ) (q : ℚ) : ℂ :=
  (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ k),
    (weight η k:ℂ)*geometricSum (5*n) (z^k))-
  (∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ 5*k),
    (weight η k:ℂ)*geometricSum n (z^(5*k)))

def main (n K : ℕ) (τ θ η : ℝ) (q : ℚ) : ℂ :=
  (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ k),
    (weight η k:ℂ)*(5*(n:ℂ))*(∫ x in (0:ℝ)..1, Complex.exp (-argument n τ θ q k*(x:ℂ))))-
  (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ 5*k),
    (weight η k:ℂ)*(n:ℂ)*(∫ x in (0:ℝ)..1, Complex.exp (-argument n τ θ q k*(x:ℂ))))

theorem split (n K : ℕ) (z : ℂ) (η : ℝ) (q : ℚ) :
    full n K z η = discrete n K z η q+nonresonant n K z η q := by
  have he (k : ℕ) : (z^k)^5 = z^(5*k) := by rw [← pow_mul,Nat.mul_comm]
  have h1 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) (fun k => q.den ∣ k)
    (fun k => (weight η k:ℂ)*geometricSum (5*n) (z^k))
  have h5 := Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 K) (fun k => q.den ∣ 5*k)
    (fun k => (weight η k:ℂ)*geometricSum n (z^(5*k)))
  unfold full discrete nonresonant
  simp_rw [fourier_block_difference,he,mul_sub]
  rw [Finset.sum_sub_distrib]
  linear_combination -h1+h5

theorem discrete_quadrature (n K : ℕ) (τ θ η : ℝ) (q : ℚ) (hn : 0 < n) :
    discrete n K (point n τ θ) η q =
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ k),
        (weight η k:ℂ)*ResonantQuadrature.finiteSum (5*n) (argument n τ θ q k))-
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ 5*k),
        (weight η k:ℂ)*ResonantQuadrature.finiteSum n (argument n τ θ q k)) := by
  unfold discrete
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    congr 1
    simpa only [one_mul] using resonant_sum n (5*n) 1 k τ θ q hn (by omega) (by omega)
      (by simpa only [one_mul] using (Finset.mem_filter.mp hk).2)
  · apply Finset.sum_congr rfl
    intro k hk
    congr 1
    exact resonant_sum n n 5 k τ θ q hn hn (by omega) (Finset.mem_filter.mp hk).2

theorem error_identity (n K : ℕ) (τ θ η : ℝ) (q : ℚ) (hn : 0 < n) :
    discrete n K (point n τ θ) η q-main n K τ θ η q =
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ k),
        (weight η k:ℂ)*ResonantErrorBudget.error (5*n) (argument n τ θ q k))-
      (∑ k ∈ (Finset.Icc 1 K).filter (fun k => q.den ∣ 5*k),
        (weight η k:ℂ)*ResonantErrorBudget.error n (argument n τ θ q k)) := by
  rw [discrete_quadrature n K τ θ η q hn]
  unfold main ResonantErrorBudget.error
  push_cast
  simp only [mul_sub,Finset.sum_sub_distrib,mul_assoc]
  ring

theorem approximation_error (n N Q K : ℕ) (τ T θ η : ℝ) (q : ℚ)
    (hN : 0 < N) (hn : N ≤ n) (hQ : 0 < Q) (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hη : 0 < η) (hη1 : η ≤ 1) (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q)
    (hZ : radiusBound N Q K T q < 2*Real.pi) :
    ‖discrete n K (point n τ θ) η q-main n K τ θ η q‖/(n:ℝ) ≤
      4*kappa (radiusBound N Q K T q)*Real.log (2/η)/(n:ℝ) := by
  rw [error_identity n K τ θ η q (by omega)]
  exact actual_resonant_error n N Q K τ T θ η q hN hn hQ hτ hT hη hη1 hq hZ

theorem full_error_identity (n K : ℕ) (τ θ η : ℝ) (q : ℚ) :
    full n K (point n τ θ) η-main n K τ θ η q =
      nonresonant n K (point n τ θ) η q+
        (discrete n K (point n τ θ) η q-main n K τ θ η q) := by
  rw [split n K (point n τ θ) η q]
  ring

theorem nonresonant_denominator_one (n K : ℕ) (z : ℂ) (η : ℝ) (q : ℚ) (hb : q.den = 1) :
    nonresonant n K z η q = 0 := by
  simp [nonresonant,hb]

theorem nonresonant_denominator_five (n K : ℕ) (z : ℂ) (η : ℝ) (q : ℚ) (hb : q.den = 5) :
    nonresonant n K z η q =
      ∑ k ∈ (Finset.Icc 1 K).filter (fun k => ¬ 5 ∣ k),
        (weight η k:ℂ)*geometricSum (5*n) (z^k) := by
  simp [nonresonant,hb]

theorem main_denominator_one (n K : ℕ) (τ θ η : ℝ) (q : ℚ) (hb : q.den = 1) :
    main n K τ θ η q = (4*(n:ℂ))*
      ∑ k ∈ Finset.Icc 1 K, (weight η k:ℂ)*
        (∫ x in (0:ℝ)..1, Complex.exp (-argument n τ θ q k*(x:ℂ))) := by
  simp only [main,hb,one_dvd,Finset.filter_true_of_mem (fun _ _ => trivial)]
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end
end Borwein.ResonantFourierSplit
