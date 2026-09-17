import Borwein.EndpointDerivativeConstants
import Mathlib.Analysis.Complex.RealDeriv

set_option autoImplicit false

namespace Borwein.EndpointRadialDifferentiation
noncomputable section
open Complex Set EndpointPhaseAtoms EndpointPhaseSeries

theorem radial_atom_deriv (c : ℝ) (j : ℕ) (v : ℝ) (hv : 0 < v) :
    HasDerivAt (fun s => atom c j s 0)
      (-((c:ℂ)*atom c j v 0+(j+1:ℕ)*atom c (j+1) v 0)) v := by
  have hd : HasDerivAt (fun s : ℝ => coordinate s 0) 1 v := by
    convert! Complex.ofRealCLM.hasDerivAt (x := v) using 1
    funext s
    simp [coordinate]
  have hh := ((hd.const_mul (-(c:ℂ))).cexp).div (hd.pow (j+1))
    (pow_ne_zero _ (coordinate_ne_zero v 0 hv))
  apply hh.congr_deriv
  simp only [atom, Pi.pow_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hz := coordinate_ne_zero v 0 hv
  simp only [pow_succ]
  field_simp
  ring

theorem radial_component_deriv (n h j : ℕ) (v : ℝ) (k : ℕ) (hv : 0 < v) :
    HasDerivAt (fun s => component n h j s 0 k)
      (-(component n (h+1) j v 0 k+(j+1:ℕ)*component n h (j+1) v 0 k)) v := by
  apply ((radial_atom_deriv (frequency n k) j v hv).const_mul
    ((coefficient k:ℂ)*(frequency n k:ℂ)^h)).congr_deriv
  simp only [component, pow_succ]
  ring

theorem majorant_antitone (n h j : ℕ) (v s : ℝ) (k : ℕ) (hv : 0 < v) (hs : v ≤ s) :
    majorant n h j s k ≤ majorant n h j v k := by
  have hf := frequency_nonneg n k
  have he : Real.exp (-frequency n k*s) ≤ Real.exp (-frequency n k*v) :=
    Real.exp_le_exp.mpr (by nlinarith)
  apply div_le_div₀ (mul_nonneg (pow_nonneg hf h) (Real.exp_pos _).le)
    (mul_le_mul_of_nonneg_left he (pow_nonneg hf h)) (by positivity : 0 < v^(j+1))
    (pow_le_pow_left₀ hv.le hs _)

theorem radial_series_deriv (n h j : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (fun s => series n h j s 0)
      (-(series n (h+1) j v 0+(j+1:ℕ)*series n h (j+1) v 0)) v := by
  let u := fun k => majorant n (h+1) j (v/2) k+((j+1:ℕ):ℝ)*majorant n h (j+1) (v/2) k
  have hv2 : 0 < v/2 := by positivity
  have hu : Summable u := (majorant_summable n (h+1) j (v/2) hn hv2).add
    ((majorant_summable n h (j+1) (v/2) hn hv2).mul_left _)
  have hb : ∀ k s, s ∈ Ioi (v/2) →
      ‖-(component n (h+1) j s 0 k+(j+1:ℕ)*component n h (j+1) s 0 k)‖ ≤ u k := by
    intro k s hs
    have hs0 : 0 < s := hv2.trans hs
    rw [norm_neg]
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_natCast]
    apply add_le_add
    · exact (component_bound n (h+1) j s 0 k hs0).trans (majorant_antitone n (h+1) j (v/2) s k hv2 hs.le)
    · exact mul_le_mul_of_nonneg_left
        ((component_bound n h (j+1) s 0 k hs0).trans (majorant_antitone n h (j+1) (v/2) s k hv2 hs.le)) (Nat.cast_nonneg _)
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (convex_Ioi (v/2)).isPreconnected
    (fun k s hs => radial_component_deriv n h j s k (hv2.trans hs)) hb
    (show v ∈ Ioi (v/2) from by change v/2 < v; linarith) (component_summable n h j v 0 hn hv)
    (show v ∈ Ioi (v/2) from by change v/2 < v; linarith)
  apply hd.congr_deriv
  exact (((component_summable n (h+1) j v 0 hn hv).hasSum.add
    ((component_summable n h (j+1) v 0 hn hv).hasSum.mul_left ((j+1:ℕ):ℂ))).neg).tsum_eq

end
end Borwein.EndpointRadialDifferentiation
