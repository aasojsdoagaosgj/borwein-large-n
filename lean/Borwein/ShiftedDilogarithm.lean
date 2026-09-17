import Borwein.DilogarithmUpper
import Borwein.SmoothedLogTail
import Borwein.SmoothedResonantMain

set_option autoImplicit false

namespace Borwein.ShiftedDilogarithm
noncomputable section
open Complex MeasureTheory SmoothedLogSeries SmoothedResonantMain Dilogarithm DilogarithmUpper

theorem integral_term (η : ℝ) (z : ℂ) (k : ℕ) (hz : z ≠ 0) :
    (∫ x in (0:ℝ)..1, filtered 1 η z k x) =
      ((Complex.exp (-(η:ℂ)))^k-(Complex.exp (-((η:ℂ)+z)))^k)/((k:ℂ)^2*z) := by
  by_cases hk : k = 0
  · subst k
    simp [filtered,SmoothedLogSeries.term]
  rw [SmoothedLogTail.integral_filtered]
  simp only [one_dvd,if_true]
  have hi := ResonantQuadrature.integral_formula ((k:ℂ)*z)
    (mul_ne_zero (by exact_mod_cast hk) hz)
  simp only [neg_mul] at hi ⊢
  rw [hi,← FiniteBlockLocalization.weight_eq,Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_exp]
  have he : Complex.exp (-((η:ℂ)+z)) = Complex.exp (-(η:ℂ))*Complex.exp (-z) := by
    rw [neg_add,Complex.exp_add]
  have hek : Complex.exp (-((k:ℂ)*z)) = (Complex.exp (-z))^k := by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  rw [he,hek,mul_pow]
  push_cast
  field_simp

theorem integral_formula (η : ℝ) (z : ℂ) (hη : 0 < η) (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    integral 1 η z = (dilog (Complex.exp (-(η:ℂ)))-dilog (Complex.exp (-((η:ℂ)+z))))/z := by
  have hq0 : ‖Complex.exp (-(η:ℂ))‖ ≤ 1 := by
    simp only [Complex.norm_exp,Complex.neg_re,Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hq1 : ‖Complex.exp (-((η:ℂ)+z))‖ ≤ 1 := by
    rw [Complex.norm_exp,Real.exp_le_one_iff]
    simp only [Complex.neg_re,Complex.add_re,Complex.ofReal_re]
    linarith
  have hs := ((hasSum_dilog _ hq0).sub (hasSum_dilog _ hq1)).div_const z
  have h : HasSum (fun k => ∫ x in (0:ℝ)..1, filtered 1 η z k x)
      ((dilog (Complex.exp (-(η:ℂ)))-dilog (Complex.exp (-((η:ℂ)+z))))/z) := by
    apply hs.congr_fun
    intro k
    rw [integral_term η z k hz0]
    ring
  exact (hasSum_integral 1 η z (by norm_num) hη hz).unique h

theorem pole_formula (η : ℝ) (z : ℂ) (hη : 0 < η) (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    poleIntegral 1 η z =
      ((dilog (Complex.exp (-((η:ℂ)+z)))-(radial η:ℂ))/z).re := by
  have hr := integral_real 1 η z (by norm_num) hη hz
  rw [integral_formula η z hη hz hz0,dilog_radial η hη.le] at hr
  norm_num only [Nat.cast_one,div_one] at hr
  have he : (dilog (Complex.exp (-((η:ℂ)+z)))-(radial η:ℂ))/z =
      -(((radial η:ℂ)-dilog (Complex.exp (-((η:ℂ)+z))))/z) := by ring
  rw [he,Complex.neg_re,hr]
  ring

theorem radial_zero : radial 0 = Real.pi^2/6 := by
  simpa [radial] using hasSum_zeta_two.tsum_eq

theorem pole_norm_upper (η : ℝ) (z : ℂ) (hη : 0 < η) (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    poleIntegral 1 η z ≤ (Real.pi^2/6)/‖z‖ := by
  have hrad : radial (η+z.re) ≤ Real.pi^2/6 := by
    rw [← radial_zero]
    exact radial_mono (by norm_num) (by linarith)
  have hd := norm_dilog_le ((η:ℂ)+z) (by simp; linarith)
  simp only [Complex.add_re,Complex.ofReal_re] at hd
  have hW := hd.trans hrad
  rw [pole_formula η z hη hz hz0,sub_div,Complex.sub_re]
  have hR : 0 ≤ (((radial η:ℂ))/z).re := by
    simp only [Complex.div_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero]
    exact div_nonneg (mul_nonneg (radial_nonneg η) hz) (Complex.normSq_nonneg z)
  have h := Complex.re_le_norm (dilog (Complex.exp (-((η:ℂ)+z)))/z)
  rw [norm_div] at h
  have hb := div_le_div_of_nonneg_right hW (norm_nonneg z)
  linarith

end
end Borwein.ShiftedDilogarithm
