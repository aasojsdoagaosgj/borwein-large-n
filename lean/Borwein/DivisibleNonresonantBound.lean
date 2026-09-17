import Borwein.NonresonantGeometricBound
import Borwein.RadialCorrectionEnvelope

set_option autoImplicit false

namespace Borwein.DivisibleNonresonantBound
noncomputable section
open Complex AngularKernel FiniteBlockLocalization ResonantGeometricSum ZeroPoleBudget
  NonresonantGeometricBound

theorem five_sine_lower (Q K B k : ℕ) (θ : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hkK : k ≤ K) (hb : q.den = 5*B)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hk : ¬ B ∣ k) :
    10*(1-(K:ℝ)/Q)/(q.den:ℝ) ≤ |Real.sin (((5*k:ℕ):ℝ)*θ/2)| := by
  have hs := residue_sine_lower (θ/(2*Real.pi)) Q hQ q hq (5*k)
  have he : Real.pi*(((5*k:ℕ):ℝ)*(θ/(2*Real.pi))) = ((5*k:ℕ):ℝ)*θ/2 := by field_simp
  rw [he] at hs
  apply le_trans _ hs
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg q.den)
  have hr := RadialCorrectionEnvelope.five_residue_ge q B k hb hk
  have hd := div_le_div_of_nonneg_right (show (k:ℝ) ≤ K by exact_mod_cast hkK) (Nat.cast_nonneg Q)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat] at *
  rw [mul_div_assoc]
  linarith

theorem five_point_bound (n M Q K B k : ℕ) (τ θ : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hKQ : K < Q) (hkK : k ≤ K) (hτ : 0 ≤ τ)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5*B) (hk : ¬ B ∣ k) :
    ‖geometricSum M ((point n τ θ)^(5*k))‖ ≤ (q.den:ℝ)/(10*(1-(K:ℝ)/Q)) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have hs := five_sine_lower Q K B k θ q hQ hkK hb hq hk
  have hpos : 0 < 10*(1-(K:ℝ)/Q)/(q.den:ℝ) := by positivity
  rw [point_pow]
  apply (geometric_bound M (Real.exp (-(((5*k:ℕ):ℝ)*τ/(5*n)))) (((5*k:ℕ):ℝ)*θ)
    (Real.exp_pos _) (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))) (hpos.trans_le hs)).trans
  have h := one_div_le_one_div_of_le hpos hs
  convert h using 1 <;> field_simp

theorem weighted_bound (s : Finset ℕ) (f : ℕ → ℂ) (η C : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hC : 0 ≤ C) (hf : ∀ k ∈ s, ‖f k‖ ≤ C) :
    ‖∑ k ∈ s, (weight η k:ℂ)*f k‖ ≤ C*Real.log (2/η) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ s, weight η k*C := by
      apply Finset.sum_le_sum
      intro k hk
      have hw : 0 ≤ weight η k := by unfold weight; positivity
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hf k hk) hw
    _ = C*∑ k ∈ s, weight η k := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ResonantErrorBudget.weight_sum_bound s η hη hη1) hC

theorem nonresonant_bound (n Q K B : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hKQ : K < Q) (hτ : 0 ≤ τ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) (hb : q.den = 5*B) :
    ‖ResonantFourierSplit.nonresonant n K (point n τ θ) η q‖ ≤
      (3*(q.den:ℝ)/(5*(1-(K:ℝ)/Q)))*Real.log (2/η) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hcut : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have h1 := weighted_bound ((Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ k))
    (fun k => geometricSum (5*n) ((point n τ θ)^k)) η ((q.den:ℝ)/(2*(1-(K:ℝ)/Q)))
    hη hη1 (by positivity) (by
      intro k hk
      exact point_geometric_bound n (5*n) Q K k τ θ q hQ hKQ
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2 hτ hq (Finset.mem_filter.mp hk).2)
  have h5 := weighted_bound ((Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ 5*k))
    (fun k => geometricSum n ((point n τ θ)^(5*k))) η ((q.den:ℝ)/(10*(1-(K:ℝ)/Q)))
    hη hη1 (by positivity) (by
      intro k hk
      have hn : ¬ B ∣ k := by
        intro hd
        exact (Finset.mem_filter.mp hk).2 (by rw [hb]; exact Nat.mul_dvd_mul_left 5 hd)
      exact five_point_bound n n Q K B k τ θ q hQ hKQ
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2 hτ hq hb hn)
  unfold ResonantFourierSplit.nonresonant
  apply (norm_sub_le _ _).trans
  apply (add_le_add h1 h5).trans_eq
  field_simp
  <;> ring

end
end Borwein.DivisibleNonresonantBound
