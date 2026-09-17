import Borwein.ResonantQuadrature
import Borwein.ZeroPoleBudget
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace Borwein.ResonantErrorBudget
noncomputable section
open Complex MeasureTheory ExponentialKernelRemainder ResonantQuadrature ZeroPoleBudget

theorem kappa_nonneg (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 2*Real.pi) : 0 ≤ kappa r := by
  have hd : 0 < 1-r^2/(4*Real.pi^2) := by
    have hs : r^2 < 4*Real.pi^2 := by nlinarith [Real.pi_pos]
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr hs)
  unfold kappa
  positivity

theorem kappa_mono (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 2*Real.pi) :
    kappa a ≤ kappa b := by
  have hb0 : 0 ≤ b := ha.trans hab
  have hd : 0 < 12*(1-b^2/(4*Real.pi^2)) := by
    have hs : b^2 < 4*Real.pi^2 := by nlinarith [Real.pi_pos]
    have hp : 0 < 1-b^2/(4*Real.pi^2) := sub_pos.mpr ((div_lt_one (by positivity)).mpr hs)
    positivity
  have hs : a^2/(4*Real.pi^2) ≤ b^2/(4*Real.pi^2) :=
    div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have he := (div_le_div_of_nonneg_left ha hd (by linarith :
    12*(1-b^2/(4*Real.pi^2)) ≤ 12*(1-a^2/(4*Real.pi^2)))).trans
    (div_le_div_of_nonneg_right hab hd.le)
  unfold kappa
  linarith

theorem weight_hasSum (η : ℝ) (hη : 0 < η) :
    HasSum (weight η) (-Real.log (1-Real.exp (-η))) := by
  have he : |Real.exp (-η)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have h := Real.hasSum_pow_div_log_of_abs_lt_one he
  have ht : HasSum (fun n : ℕ => weight η (n+1)) (-Real.log (1-Real.exp (-η))) := by
    convert! h using 1
    funext n
    unfold weight
    rw [← Real.exp_nat_mul]
    push_cast
    congr 2; ring
  apply (hasSum_nat_add_iff' 1).mp
  simpa [weight] using ht

theorem log_weight_budget (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    -Real.log (1-Real.exp (-η)) ≤ Real.log (2/η) := by
  have he := Real.add_one_le_exp η
  have hi : (Real.exp η)⁻¹ ≤ (η+1)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity) he
  have hx : η/2 ≤ 1-(η+1)⁻¹ := by
    have hid : 1-(η+1)⁻¹ = η/(η+1) := by field_simp; ring
    rw [hid]
    apply (le_div_iff₀ (by positivity : 0 < η+1)).mpr
    have : η^2 ≤ η := by nlinarith
    nlinarith
  have hdelta : η/2 ≤ 1-Real.exp (-η) := by rw [Real.exp_neg]; linarith
  have hl := Real.log_le_log (by positivity : 0 < η/2) hdelta
  have hid : -Real.log (η/2) = Real.log (2/η) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  rw [← hid]
  linarith

theorem weight_sum_bound (s : Finset ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (∑ k ∈ s, weight η k) ≤ Real.log (2/η) := by
  have hs := weight_hasSum η hη
  have h := Summable.sum_le_tsum s (fun k _ => by unfold weight; positivity) hs.summable
  rw [hs.tsum_eq] at h
  exact h.trans (log_weight_budget η hη hη1)

def error (M : ℕ) (A : ℂ) : ℂ :=
  finiteSum M A-(M:ℂ)*(∫ x in (0:ℝ)..1, Complex.exp (-A*(x:ℂ)))

theorem weighted_error_bound (s : Finset ℕ) (M : ℕ) (A : ℕ → ℂ) (η Z : ℝ)
    (hM : 0 < M) (hη : 0 < η) (hη1 : η ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z < 2*Real.pi)
    (hA0 : ∀ k ∈ s, 0 ≤ (A k).re) (hA : ∀ k ∈ s, ‖A k/(M:ℂ)‖ ≤ Z) :
    ‖∑ k ∈ s, (weight η k:ℂ)*error M (A k)‖ ≤ 2*kappa Z*Real.log (2/η) := by
  have hb (k : ℕ) (hk : k ∈ s) : ‖error M (A k)‖ ≤ 2*kappa Z := by
    have he := error_bound M (A k) hM (hA0 k hk) ((hA k hk).trans_lt hZ)
    exact he.trans (mul_le_mul_of_nonneg_left (kappa_mono _ _ (norm_nonneg _) (hA k hk) hZ) (by norm_num))
  have ht : ‖∑ k ∈ s, (weight η k:ℂ)*error M (A k)‖ ≤ ∑ k ∈ s, weight η k*(2*kappa Z) := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (by unfold weight; positivity)]
    exact mul_le_mul_of_nonneg_left (hb k hk) (by unfold weight; positivity)
  have heq : (∑ k ∈ s, weight η k*(2*kappa Z)) = 2*kappa Z*(∑ k ∈ s, weight η k) := by
    rw [← Finset.sum_mul]
    ring
  rw [heq] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (weight_sum_bound s η hη hη1)
    (mul_nonneg (by norm_num) (kappa_nonneg Z hZ0 hZ)))

theorem two_sums_bound (s₁ s₅ : Finset ℕ) (n : ℕ) (A : ℕ → ℂ) (η Z : ℝ)
    (hn : 0 < n) (hη : 0 < η) (hη1 : η ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z < 2*Real.pi)
    (hA0 : ∀ k ∈ s₁ ∪ s₅, 0 ≤ (A k).re)
    (hA : ∀ k ∈ s₁ ∪ s₅, ‖A k/(n:ℂ)‖ ≤ Z) :
    ‖(∑ k ∈ s₁, (weight η k:ℂ)*error (5*n) (A k))-
      (∑ k ∈ s₅, (weight η k:ℂ)*error n (A k))‖/(n:ℝ) ≤
      4*kappa Z*Real.log (2/η)/(n:ℝ) := by
  have h5 : ∀ k ∈ s₁, ‖A k/((5*n:ℕ):ℂ)‖ ≤ Z := by
    intro k hk
    have h := hA k (Finset.mem_union.mpr (Or.inl hk))
    rw [norm_div,Complex.norm_natCast] at h ⊢
    apply le_trans _ h
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by exact_mod_cast hn)
      (by norm_num; nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have h1 := weighted_error_bound s₁ (5*n) A η Z (by omega) hη hη1 hZ0 hZ
    (fun k hk => hA0 k (Finset.mem_union.mpr (Or.inl hk))) h5
  have h5' := weighted_error_bound s₅ n A η Z hn hη hη1 hZ0 hZ
    (fun k hk => hA0 k (Finset.mem_union.mpr (Or.inr hk)))
    (fun k hk => hA k (Finset.mem_union.mpr (Or.inr hk)))
  have ht := (norm_sub_le _ _).trans (add_le_add h1 h5')
  have he : 2*kappa Z*Real.log (2/η)+2*kappa Z*Real.log (2/η) =
      4*kappa Z*Real.log (2/η) := by ring
  rw [he] at ht
  exact div_le_div_of_nonneg_right ht (Nat.cast_nonneg n)

end
end Borwein.ResonantErrorBudget
