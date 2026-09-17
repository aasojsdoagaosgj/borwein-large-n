import Borwein.EndpointFiniteTailExpansion
import Mathlib.Analysis.Calculus.SmoothSeries

set_option autoImplicit false

namespace Borwein.EndpointPhaseAtoms
noncomputable section
open Complex

def coordinate (v y : ℝ) : ℂ := (v:ℂ)+(y:ℂ)*I
def atom (c : ℝ) (j : ℕ) (v y : ℝ) : ℂ := exp (-(c:ℂ)*coordinate v y)/coordinate v y^(j+1)
def coefficient (k : ℕ) : ℝ := (if 5 ∣ k then 4 else -1)/(5*(k:ℝ)^2)
def frequency (n k : ℕ) : ℝ := (5*n:ℕ)*k
def component (n h j : ℕ) (v y : ℝ) (k : ℕ) : ℂ :=
  (coefficient k:ℂ)*(frequency n k:ℂ)^h*atom (frequency n k) j v y

theorem coordinate_re (v y : ℝ) : (coordinate v y).re=v := by simp [coordinate]

theorem coordinate_ne_zero (v y : ℝ) (hv : 0 < v) : coordinate v y ≠ 0 := by
  intro he
  have := congrArg Complex.re he
  simp only [coordinate_re, Complex.zero_re] at this
  linarith

theorem coordinate_norm (v y : ℝ) : v ≤ ‖coordinate v y‖ := by
  simpa only [coordinate_re] using Complex.re_le_norm (coordinate v y)

theorem coordinate_deriv (v y : ℝ) : HasDerivAt (coordinate v) I y := by
  have hi : HasDerivAt (fun y : ℝ => (y:ℂ)) 1 y := by
    convert! Complex.ofRealCLM.hasDerivAt (x := y) using 1
  convert! (hi.mul_const I).const_add (v:ℂ) using 1 <;> simp [coordinate]

theorem atom_deriv (c : ℝ) (j : ℕ) (v y : ℝ) (hv : 0 < v) :
    HasDerivAt (atom c j v) (-I*((c:ℂ)*atom c j v y+(j+1:ℕ)*atom c (j+1) v y)) y := by
  have hd := coordinate_deriv v y
  have hn := (hd.const_mul (-(c:ℂ))).cexp
  have hh := hn.div (hd.pow (j+1)) (pow_ne_zero _ (coordinate_ne_zero v y hv))
  apply hh.congr_deriv
  simp only [atom, Pi.pow_apply, Pi.mul_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hz := coordinate_ne_zero v y hv
  simp only [pow_succ]
  field_simp
  ring

theorem atom_bound (c : ℝ) (j : ℕ) (v y : ℝ) (hv : 0 < v) :
    ‖atom c j v y‖ ≤ Real.exp (-c*v)/v^(j+1) := by
  rw [atom, norm_div, Complex.norm_exp, norm_pow]
  have he : (-(c:ℂ)*coordinate v y).re = -c*v := by simp [coordinate, Complex.mul_re]
  rw [he]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
    (pow_le_pow_left₀ hv.le (coordinate_norm v y) _)

theorem coefficient_zero : coefficient 0=0 := by simp [coefficient]

theorem coefficient_bound (k : ℕ) : |coefficient k| ≤ 1 := by
  by_cases hk : k=0
  · simp [hk, coefficient_zero]
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hd : (0:ℝ) < 5*(k:ℝ)^2 := by positivity
  rw [coefficient, abs_div, abs_of_pos hd]
  apply (div_le_one hd).mpr
  split_ifs <;> norm_num <;> nlinarith

theorem frequency_nonneg (n k : ℕ) : 0 ≤ frequency n k := by unfold frequency; positivity

theorem component_deriv (n h j : ℕ) (v y : ℝ) (k : ℕ) (hv : 0 < v) :
    HasDerivAt (fun y => component n h j v y k)
      (-I*(component n (h+1) j v y k+(j+1:ℕ)*component n h (j+1) v y k)) y := by
  have hh := (atom_deriv (frequency n k) j v y hv).const_mul ((coefficient k:ℂ)*(frequency n k:ℂ)^h)
  apply hh.congr_deriv
  simp only [component, pow_succ]
  ring

theorem component_bound (n h j : ℕ) (v y : ℝ) (k : ℕ) (hv : 0 < v) :
    ‖component n h j v y k‖ ≤
      frequency n k^h*Real.exp (-frequency n k*v)/v^(j+1) := by
  rw [component, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (frequency_nonneg n k)]
  have h1 := mul_le_mul_of_nonneg_right (coefficient_bound k) (pow_nonneg (frequency_nonneg n k) h)
  rw [one_mul] at h1
  have h2 := mul_le_mul h1 (atom_bound (frequency n k) j v y hv) (norm_nonneg _) (pow_nonneg (frequency_nonneg n k) h)
  exact h2.trans_eq (by ring)

end
end Borwein.EndpointPhaseAtoms
