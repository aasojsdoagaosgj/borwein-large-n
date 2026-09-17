import Borwein.PoleVariation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Borwein.FivePoleDecomposition
noncomputable section
open scoped BigOperators

theorem root_sum (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (k : Fin 5) :
    (∑ j : Fin 5, ζ^(j.val*k.val)) = if k = 0 then 5 else 0 := by
  by_cases hk : k = 0
  · simp [hk]
  · rw [if_neg hk]
    have hc : k.val.Coprime 5 := by
      have hlo : 0 < k.val := Nat.pos_of_ne_zero (fun h => hk (Fin.ext h))
      have hhi := k.isLt
      interval_cases k.val <;> norm_num
    have h := (hζ.pow_of_coprime k.val hc).geom_sum_eq_zero (by norm_num : 1 < 5)
    rw [← Fin.sum_univ_eq_sum_range] at h
    simpa only [← pow_mul, Nat.mul_comm k.val] using h

theorem rotated_power (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (j : ℕ) :
    (ζ^j*z)^5 = z^5 := by
  rw [mul_pow, show (ζ^j)^5=(ζ^5)^j by simp only [← pow_mul]; congr 1; omega,
    hζ.pow_eq_one, one_pow, one_mul]

theorem pole_geometric (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (hz : z^5 ≠ 1)
    (j : Fin 5) :
    (1-ζ^j.val*z)⁻¹ = (∑ k : Fin 5, (ζ^j.val*z)^k.val)/(1-z^5) := by
  have hw : ζ^j.val*z ≠ 1 := by
    intro he
    have hh := rotated_power ζ z hζ j.val
    rw [he, one_pow] at hh
    exact hz hh.symm
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hw, rotated_power ζ z hζ]
  have hn : 1-z^5 ≠ 0 := sub_ne_zero.mpr hz.symm
  have hn' : ζ^j.val*z-1 ≠ 0 := sub_ne_zero.mpr hw
  have hn'' : 1-ζ^j.val*z ≠ 0 := sub_ne_zero.mpr hw.symm
  field_simp
  ring

theorem sum_five_poles (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (hz : z^5 ≠ 1) :
    (∑ j : Fin 5, (1-ζ^j.val*z)⁻¹) = 5/(1-z^5) := by
  simp_rw [pole_geometric ζ z hζ hz]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [mul_pow, ← pow_mul, ← Finset.sum_mul, root_sum ζ hζ]
  simp

theorem kernel_difference (z : ℂ) (hz : z^5 ≠ 1) :
    FiniteFourierKernel.kernel z = (1-z)⁻¹-(1-z^5)⁻¹ := by
  have hz1 : z ≠ 1 := by intro h; exact hz (by simp [h])
  have hn : 1-z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have hn5 : 1-z^5 ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold FiniteFourierKernel.kernel
  field_simp
  ring

theorem five_pole_decomposition (ζ z : ℂ) (hζ : IsPrimitiveRoot ζ 5) (hz : z^5 ≠ 1) :
    FiniteFourierKernel.kernel z =
      (4/5:ℂ)*(1-z)⁻¹-(1/5:ℂ)*∑ j : Fin 4, (1-ζ^(j.val+1)*z)⁻¹ := by
  have h := sum_five_poles ζ z hζ hz
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ] at h
  rw [kernel_difference z hz]
  linear_combination (1/5:ℂ)*h

theorem kernel_variation (ζ z w : ℂ) (hζ : IsPrimitiveRoot ζ 5)
    (hz : z^5 ≠ 1) (hw : w^5 ≠ 1) :
    ‖FiniteFourierKernel.kernel z-FiniteFourierKernel.kernel w‖ ≤
      (4/5:ℝ)*‖(1-z)⁻¹-(1-w)⁻¹‖+
      (1/5:ℝ)*∑ j : Fin 4, ‖(1-ζ^(j.val+1)*z)⁻¹-(1-ζ^(j.val+1)*w)⁻¹‖ := by
  have he : FiniteFourierKernel.kernel z-FiniteFourierKernel.kernel w =
      (4/5:ℂ)*((1-z)⁻¹-(1-w)⁻¹)-
      (1/5:ℂ)*∑ j : Fin 4, ((1-ζ^(j.val+1)*z)⁻¹-(1-ζ^(j.val+1)*w)⁻¹) := by
    rw [five_pole_decomposition ζ z hζ hz, five_pole_decomposition ζ w hζ hw,
      Finset.sum_sub_distrib]
    ring
  rw [he]
  have ht := norm_sub_le
    ((4/5:ℂ)*((1-z)⁻¹-(1-w)⁻¹))
    ((1/5:ℂ)*∑ j : Fin 4, ((1-ζ^(j.val+1)*z)⁻¹-(1-ζ^(j.val+1)*w)⁻¹))
  norm_num only [norm_mul, norm_div, norm_one, Complex.norm_ofNat] at ht
  refine ht.trans (add_le_add le_rfl ?_)
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)

end
end Borwein.FivePoleDecomposition
