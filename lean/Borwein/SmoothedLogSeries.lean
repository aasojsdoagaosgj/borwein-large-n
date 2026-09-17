import Borwein.ResonantErrorBudget
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace Borwein.SmoothedLogSeries
noncomputable section
open Complex MeasureTheory ZeroPoleBudget

def term (η : ℝ) (z : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-(k:ℂ)*((η:ℂ)+z*(x:ℂ)))/(k:ℂ)

def filtered (b : ℕ) (η : ℝ) (z : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  if b ∣ k then term η z k x else 0

def logValue (b : ℕ) (η : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  -Complex.log (1-Complex.exp (-(b:ℂ)*((η:ℂ)+z*(x:ℂ))))/(b:ℂ)

theorem term_weighted (η : ℝ) (z : ℂ) (k : ℕ) (x : ℝ) :
    term η z k x = (weight η k:ℂ)*Complex.exp (-(k:ℂ)*z*(x:ℂ)) := by
  unfold term weight
  rw [Complex.ofReal_div,Complex.ofReal_exp]
  push_cast
  rw [show -(k:ℂ)*((η:ℂ)+z*(x:ℂ)) = -(η:ℂ)*(k:ℂ)+(-(k:ℂ)*z*(x:ℂ)) by ring,
    Complex.exp_add]
  ring

theorem term_continuous (η : ℝ) (z : ℂ) (k : ℕ) : Continuous (term η z k) := by
  unfold term
  fun_prop

theorem norm_term_le (η : ℝ) (z : ℂ) (k : ℕ) (x : ℝ) (hz : 0 ≤ z.re) (hx : 0 ≤ x) :
    ‖term η z k x‖ ≤ weight η k := by
  rw [term_weighted,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by unfold weight; positivity),
    Complex.norm_exp]
  have he : (-(k:ℂ)*z*(x:ℂ)).re ≤ 0 := by
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.natCast_re,Complex.natCast_im,
      Complex.ofReal_re,Complex.ofReal_im,neg_zero,mul_zero,zero_mul,sub_zero]
    nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) k) hz) hx]
  exact mul_le_of_le_one_right (by unfold weight; positivity) (Real.exp_le_one_iff.mpr he)

theorem hasSum_term (η : ℝ) (z : ℂ) (x : ℝ) (hη : 0 < η) (hz : 0 ≤ z.re) (hx : 0 ≤ x) :
    HasSum (fun k => term η z k x) (-Complex.log (1-Complex.exp (-((η:ℂ)+z*(x:ℂ))))) := by
  have he : ‖Complex.exp (-((η:ℂ)+z*(x:ℂ)))‖ < 1 := by
    rw [Complex.norm_exp,Real.exp_lt_one_iff]
    simp only [Complex.neg_re,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      mul_zero,sub_zero]
    nlinarith [mul_nonneg hz hx]
  convert! Complex.hasSum_taylorSeries_neg_log he using 1
  funext k
  unfold term
  rw [← Complex.exp_nat_mul]
  congr 2
  ring

theorem term_multiple (b k : ℕ) (η : ℝ) (z : ℂ) (x : ℝ) :
    term η z (b*k) x = (1/(b:ℂ))*term ((b:ℝ)*η) ((b:ℂ)*z) k x := by
  unfold term
  have he : -((b*k:ℕ):ℂ)*((η:ℂ)+z*(x:ℂ)) =
      -(k:ℂ)*((((b:ℝ)*η:ℝ):ℂ)+((b:ℂ)*z)*(x:ℂ)) := by push_cast; ring
  rw [he]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem hasSum_filtered (b : ℕ) (η : ℝ) (z : ℂ) (x : ℝ)
    (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) (hx : 0 ≤ x) :
    HasSum (fun k => filtered b η z k x) (logValue b η z x) := by
  have hg : Function.Injective (fun k : ℕ => b*k) := by
    intro j k he
    exact Nat.mul_left_cancel (by omega : 0 < b) he
  have hs := (hasSum_term ((b:ℝ)*η) ((b:ℂ)*z) x (by positivity)
    (by simp; positivity) hx).mul_left (1/(b:ℂ))
  apply (hg.hasSum_iff (fun k hk => by
    have hd : ¬ b ∣ k := by
      rintro ⟨j,hj⟩
      exact hk ⟨j,hj.symm⟩
    simp [filtered,hd])).mp
  have he : (((b:ℝ)*η:ℝ):ℂ)+((b:ℂ)*z)*(x:ℂ) = (b:ℂ)*((η:ℂ)+z*(x:ℂ)) := by
    push_cast
    ring
  rw [he] at hs
  convert! hs using 1
  · funext k
    simp only [Function.comp_apply,filtered,dvd_mul_right,if_true,term_multiple]
  · unfold logValue
    ring

theorem filtered_continuous (b : ℕ) (η : ℝ) (z : ℂ) (k : ℕ) :
    Continuous (filtered b η z k) := by
  unfold filtered
  split_ifs
  · exact term_continuous η z k
  · exact continuous_const

theorem norm_filtered_le (b : ℕ) (η : ℝ) (z : ℂ) (k : ℕ) (x : ℝ)
    (hz : 0 ≤ z.re) (hx : 0 ≤ x) : ‖filtered b η z k x‖ ≤ weight η k := by
  unfold filtered
  split_ifs
  · exact norm_term_le η z k x hz hx
  · simp only [norm_zero]
    unfold weight
    positivity

theorem hasSum_integral (b : ℕ) (η : ℝ) (z : ℂ) (hb : 0 < b) (hη : 0 < η) (hz : 0 ≤ z.re) :
    HasSum (fun k => ∫ x in (0:ℝ)..1, filtered b η z k x)
      (∫ x in (0:ℝ)..1, logValue b η z x) := by
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k (_ : ℝ) => weight η k) (fun k => (filtered_continuous b η z k).aestronglyMeasurable)
  · intro k
    apply ae_of_all
    intro x hx
    have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by simpa using hx
    exact norm_filtered_le b η z k x hz hx'.1.le
  · exact ae_of_all _ (fun _ _ => (ResonantErrorBudget.weight_hasSum η hη).summable)
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro x hx
    have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by simpa using hx
    exact hasSum_filtered b η z x hb hη hz hx'.1.le

end
end Borwein.SmoothedLogSeries
