import Borwein.CenteredCharacteristic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace Borwein.CharacteristicLogDerivatives
noncomputable section
open Complex CenteredCharacteristic

def jet (k : ℕ) (y t : ℝ) : ℂ := I^k*moment k y t
def logValue (y t : ℝ) : ℂ := Complex.log (jet 0 y t)
def logFirst (y t : ℝ) : ℂ := jet 1 y t/jet 0 y t
def logSecond (y t : ℝ) : ℂ := jet 2 y t/jet 0 y t-(jet 1 y t)^2/(jet 0 y t)^2
def logThird (y t : ℝ) : ℂ := jet 3 y t/jet 0 y t-
  3*jet 2 y t*jet 1 y t/(jet 0 y t)^2+2*(jet 1 y t)^3/(jet 0 y t)^3
def logFourth (y t : ℝ) : ℂ := jet 4 y t/jet 0 y t-
  4*jet 3 y t*jet 1 y t/(jet 0 y t)^2-3*(jet 2 y t)^2/(jet 0 y t)^2+
  12*jet 2 y t*(jet 1 y t)^2/(jet 0 y t)^3-6*(jet 1 y t)^4/(jet 0 y t)^4

theorem jet_zero (y t : ℝ) : jet 0 y t = characteristic y t := by simp [jet,characteristic]

theorem jet_deriv (k : ℕ) (y t : ℝ) : HasDerivAt (jet k y) (jet (k+1) y t) t := by
  unfold jet
  convert! (moment_deriv k y t).const_mul (I^k) using 1
  rw [pow_succ]
  ring

theorem jet_nonzero (y t : ℝ) (ht : |t| ≤ 2/5) : jet 0 y t ≠ 0 := by
  rw [jet_zero]
  exact characteristic_ne_zero y t ht

theorem log_deriv (y t : ℝ) (ht : |t| ≤ 2/5) :
    HasDerivAt (logValue y) (logFirst y t) t := by
  exact (jet_deriv 0 y t).clog_real (by rw [jet_zero]; exact characteristic_slit y t ht)

theorem first_deriv (y t : ℝ) (ht : |t| ≤ 2/5) :
    HasDerivAt (logFirst y) (logSecond y t) t := by
  have hn := jet_nonzero y t ht
  have h := (jet_deriv 1 y t).div (jet_deriv 0 y t) hn
  unfold logFirst logSecond
  convert! h using 1
  field_simp <;> ring

theorem second_deriv (y t : ℝ) (ht : |t| ≤ 2/5) :
    HasDerivAt (logSecond y) (logThird y t) t := by
  have hn := jet_nonzero y t ht
  have h := ((jet_deriv 2 y t).div (jet_deriv 0 y t) hn).sub
    (((jet_deriv 1 y t).pow 2).div ((jet_deriv 0 y t).pow 2) (pow_ne_zero 2 hn))
  unfold logSecond logThird
  convert! h using 1
  simp only [Pi.pow_apply,Pi.mul_apply]
  field_simp <;> ring

theorem third_deriv (y t : ℝ) (ht : |t| ≤ 2/5) :
    HasDerivAt (logThird y) (logFourth y t) t := by
  have hn := jet_nonzero y t ht
  have h := (((jet_deriv 3 y t).div (jet_deriv 0 y t) hn).sub
    ((((jet_deriv 2 y t).const_mul 3).mul (jet_deriv 1 y t)).div
      ((jet_deriv 0 y t).pow 2) (pow_ne_zero 2 hn))).add
    ((((jet_deriv 1 y t).pow 3).const_mul 2).div
      ((jet_deriv 0 y t).pow 3) (pow_ne_zero 3 hn))
  unfold logThird logFourth
  convert! h using 1
  simp only [Pi.pow_apply,Pi.mul_apply]
  field_simp <;> ring

theorem jet_norm (k : ℕ) (y t : ℝ) : ‖jet k y t‖ = ‖moment k y t‖ := by
  simp [jet,norm_mul,norm_pow]

end
end Borwein.CharacteristicLogDerivatives
