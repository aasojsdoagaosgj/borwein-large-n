import Borwein.PeanoQuadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Borwein.SecondOrderSegment
noncomputable section
open Set MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem remainder_identity (f0 f1 f2 : ℝ → F)
    (h0 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (h2 : ContinuousOn f2 (Icc (0:ℝ) 1)) :
    f0 1-f0 0-f1 0 = ∫ t in (0:ℝ)..1, (1-t) • f2 t := by
  have hi1 : IntervalIntegrable f1 volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
    exact fun t ht => (h1 t ht).continuousAt.continuousWithinAt
  have hi2 : IntervalIntegrable f2 volume 0 1 := h2.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => h0 t (by simpa using ht)) hi1
  have hp := intervalIntegral.integral_smul_deriv_eq_deriv_smul
    (fun t (_ : t ∈ uIcc (0:ℝ) 1) => (hasDerivAt_id t).const_sub 1)
    (fun t ht => h1 t (by simpa using ht))
    (intervalIntegrable_const (c := (-1:ℝ))) hi2
  simp only [id_eq,sub_self,zero_smul,sub_zero,one_smul,neg_one_smul,
    intervalIntegral.integral_neg,he] at hp
  rw [hp]
  abel

theorem remainder_bound (f0 f1 f2 : ℝ → F) (C : ℝ)
    (h0 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f0 (f1 t) t)
    (h1 : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt f1 (f2 t) t)
    (h2 : ContinuousOn f2 (Icc (0:ℝ) 1))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, ‖f2 t‖ ≤ C) :
    ‖f0 1-f0 0-f1 0‖ ≤ C/2 := by
  rw [remainder_identity f0 f1 f2 h0 h1 h2]
  have hc : ContinuousOn (fun t : ℝ => (1-t) • f2 t) (Icc (0:ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).smul h2
  calc
    _ ≤ ∫ t in (0:ℝ)..1, ‖(1-t) • f2 t‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0:ℝ) ≤ 1)
    _ ≤ ∫ t in (0:ℝ)..1, (1-t)*C := by
      apply intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
        (hc.norm.intervalIntegrable_of_Icc (by norm_num))
        ((by fun_prop : Continuous (fun t : ℝ => (1-t)*C)).intervalIntegrable 0 1)
      intro t ht
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ht.2)]
      exact mul_le_mul_of_nonneg_left (hb t ht) (sub_nonneg.mpr ht.2)
    _ = C/2 := by
      rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_sub
        (intervalIntegrable_const (c := (1:ℝ)))
        ((by fun_prop : Continuous (fun t : ℝ => t)).intervalIntegrable 0 1),
        intervalIntegral.integral_const,integral_id]
      norm_num
      ring

end
end Borwein.SecondOrderSegment
