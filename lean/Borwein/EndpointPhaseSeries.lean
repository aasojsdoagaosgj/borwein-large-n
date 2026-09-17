import Borwein.EndpointPhaseAtoms

set_option autoImplicit false

namespace Borwein.EndpointPhaseSeries
noncomputable section
open Complex EndpointPhaseAtoms

def majorant (n h j : ℕ) (v : ℝ) (k : ℕ) : ℝ :=
  frequency n k^h*Real.exp (-frequency n k*v)/v^(j+1)
def series (n h j : ℕ) (v y : ℝ) : ℂ := ∑' k : ℕ, component n h j v y k

theorem geometric_identity (n k : ℕ) (v : ℝ) :
    Real.exp (-frequency n k*v)=Real.exp (-((5*n:ℕ):ℝ)*v)^k := by
  rw [← Real.exp_nat_mul]
  unfold frequency
  congr 1
  push_cast
  ring

theorem majorant_summable (n h j : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Summable (majorant n h j v) := by
  have hr : ‖Real.exp (-((5*n:ℕ):ℝ)*v)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    have : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    push_cast
    nlinarith
  have hs := ((summable_pow_mul_geometric_of_norm_lt_one h hr).mul_left (((5*n:ℕ):ℝ)^h)).div_const (v^(j+1))
  apply hs.congr
  intro k
  rw [majorant, geometric_identity, frequency, mul_pow]
  ring

theorem component_summable (n h j : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Summable (component n h j v y) :=
  (majorant_summable n h j v hn hv).of_norm_bounded (fun k => component_bound n h j v y k hv)

theorem series_deriv (n h j : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasDerivAt (series n h j v)
      (-I*(series n (h+1) j v y+(j+1:ℕ)*series n h (j+1) v y)) y := by
  let u := fun k => majorant n (h+1) j v k+((j+1:ℕ):ℝ)*majorant n h (j+1) v k
  have hu : Summable u := (majorant_summable n (h+1) j v hn hv).add
    ((majorant_summable n h (j+1) v hn hv).mul_left _)
  have hb : ∀ k y, ‖-I*(component n (h+1) j v y k+(j+1:ℕ)*component n h (j+1) v y k)‖ ≤ u k := by
    intro k y
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
    apply (norm_add_le _ _).trans
    rw [norm_mul, Complex.norm_natCast]
    exact add_le_add (component_bound n (h+1) j v y k hv)
      (mul_le_mul_of_nonneg_left (component_bound n h (j+1) v y k hv) (Nat.cast_nonneg _))
  have hd := hasDerivAt_tsum hu (fun k y => component_deriv n h j v y k hv) hb
    (component_summable n h j v 0 hn hv) y
  apply hd.congr_deriv
  exact (((component_summable n (h+1) j v y hn hv).hasSum.add
    ((component_summable n h (j+1) v y hn hv).hasSum.mul_left ((j+1:ℕ):ℂ))).mul_left (-I)).tsum_eq

theorem series_continuous (n h j : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    Continuous (series n h j v) := continuous_iff_continuousAt.mpr
      (fun y => (series_deriv n h j v y hn hv).continuousAt)

theorem series_bound (n h j : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    ‖series n h j v y‖ ≤ ∑' k : ℕ, majorant n h j v k := by
  exact norm_tsum_le_tsum_norm (component_summable n h j v y hn hv).norm |>.trans
    ((component_summable n h j v y hn hv).norm.tsum_le_tsum
      (fun k => component_bound n h j v y k hv) (majorant_summable n h j v hn hv))

end
end Borwein.EndpointPhaseSeries
