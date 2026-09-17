import Borwein.SecondOrderSegment

namespace Borwein.HigherOrderSegment
noncomputable section
open Set MeasureTheory

def weight (k : ℕ) (t : ℝ) : ℝ := (1-t)^k/(k.factorial:ℝ)

theorem weight_succ_deriv (k : ℕ) (t : ℝ) :
    HasDerivAt (weight (k+1)) (-weight k t) t := by
  have h := (((hasDerivAt_id t).const_sub 1).pow (k+1)).div_const ((k+1).factorial:ℝ)
  unfold weight
  convert! h using 1
  simp only [id_eq,Nat.add_sub_cancel,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hk : (k:ℝ)+1 ≠ 0 := by positivity
  have hf : (k.factorial:ℝ) ≠ 0 := by positivity
  field_simp <;> ring

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem weighted_step (k : ℕ) (g g' : ℝ → F)
    (hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Icc (0:ℝ) 1)) :
    (∫ t in (0:ℝ)..1, weight (k+1) t • g' t) =
      -(1/((k+1).factorial:ℝ)) • g 0 + ∫ t in (0:ℝ)..1, weight k t • g t := by
  have hw : Continuous (fun t : ℝ => -weight k t) := by unfold weight; fun_prop
  have hp := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun t (_ : t ∈ uIcc (0:ℝ) 1) => weight_succ_deriv k t)
    (fun t ht => hd t (by simpa using ht)) (hw.intervalIntegrable 0 1)
    (hc.intervalIntegrable_of_Icc (by norm_num))
  have h1 : weight (k+1) 1 = 0 := by simp [weight]
  have h0 : weight (k+1) 0 = 1/((k+1).factorial:ℝ) := by simp [weight]
  simpa only [h1,h0,zero_smul,zero_sub,neg_smul,intervalIntegral.integral_neg,sub_neg_eq_add] using hp

theorem weighted_norm_bound (k : ℕ) (f : ℝ → F) (C : ℝ)
    (hc : ContinuousOn f (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖f t‖ ≤ C) :
    ‖∫ t in (0:ℝ)..1, weight k t • f t‖ ≤ C/((k+1).factorial:ℝ) := by
  have hw : Continuous (weight k) := by unfold weight; fun_prop
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖weight k t • f t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)
    _ ≤ ∫ t in (0:ℝ)..1, weight k t*C := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
        ((hw.continuousOn.smul hc).norm.intervalIntegrable_of_Icc (by norm_num))
        ((hw.mul_const C).intervalIntegrable 0 1)
      intro t ht
      have ht0 : 0 ≤ weight k t := by
        exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) k) (by positivity)
      change ‖weight k t • f t‖ ≤ weight k t*C
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_left (hb t ht) ht0
    _ = _ := by
      rw [intervalIntegral.integral_mul_const]
      unfold weight
      rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_sub_left (fun t : ℝ => t^k) 1]
      simp only [sub_self,sub_zero,integral_pow,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      simp only [one_pow,zero_pow (Nat.succ_ne_zero k),sub_zero]
      field_simp <;> ring

theorem cubic_identity (f0 f1 f2 f3 : ℝ → F)
    (h0 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (h2 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 t) t)
    (h3 : ContinuousOn f3 (Icc (0:ℝ) 1)) :
    f0 1-f0 0-f1 0-(1/2:ℝ) • f2 0 = ∫ t in (0:ℝ)..1, weight 2 t • f3 t := by
  have hc2 : ContinuousOn f2 (Icc (0:ℝ) 1) := fun t ht => (h2 t ht).continuousAt.continuousWithinAt
  have hs := SecondOrderSegment.remainder_identity f0 f1 f2 h0 h1 hc2
  have hp := weighted_step 1 f2 f3 h2 h3
  norm_num [weight] at hp
  rw [← hs] at hp
  norm_num [weight]
  rw [hp]
  module

theorem quartic_identity (f0 f1 f2 f3 f4 : ℝ → F)
    (h0 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (h2 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 t) t)
    (h3 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f3 (f4 t) t)
    (h4 : ContinuousOn f4 (Icc (0:ℝ) 1)) :
    f0 1-f0 0-f1 0-(1/2:ℝ) • f2 0-(1/6:ℝ) • f3 0 =
      ∫ t in (0:ℝ)..1, weight 3 t • f4 t := by
  have hc3 : ContinuousOn f3 (Icc (0:ℝ) 1) := fun t ht => (h3 t ht).continuousAt.continuousWithinAt
  have hs := cubic_identity f0 f1 f2 f3 h0 h1 h2 hc3
  have hp := weighted_step 2 f3 f4 h3 h4
  norm_num only [show (2:ℕ)+1=3 by decide,show ((3:ℕ).factorial:ℝ)=6 by norm_num] at hp
  rw [← hs] at hp
  rw [hp]
  module

theorem cubic_bound (f0 f1 f2 f3 : ℝ → F) (C : ℝ)
    (h0 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (h2 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 t) t)
    (h3 : ContinuousOn f3 (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖f3 t‖ ≤ C) :
    ‖f0 1-f0 0-f1 0-(1/2:ℝ) • f2 0‖ ≤ C/6 := by
  rw [cubic_identity f0 f1 f2 f3 h0 h1 h2 h3]
  simpa only [show ((2+1:ℕ).factorial:ℝ)=6 by norm_num] using weighted_norm_bound 2 f3 C h3 hb

theorem quartic_bound (f0 f1 f2 f3 f4 : ℝ → F) (C : ℝ)
    (h0 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (h2 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f2 (f3 t) t)
    (h3 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f3 (f4 t) t)
    (h4 : ContinuousOn f4 (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖f4 t‖ ≤ C) :
    ‖f0 1-f0 0-f1 0-(1/2:ℝ) • f2 0-(1/6:ℝ) • f3 0‖ ≤ C/24 := by
  rw [quartic_identity f0 f1 f2 f3 f4 h0 h1 h2 h3 h4]
  simpa only [show ((3+1:ℕ).factorial:ℝ)=24 by norm_num] using weighted_norm_bound 3 f4 C h4 hb

end
end Borwein.HigherOrderSegment
