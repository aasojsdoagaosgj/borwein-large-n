import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Rat.Floor

namespace Borwein.SineCertificate
noncomputable section
open scoped BigOperators

def taylor (x : ℝ) (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, ((x : ℂ)*Complex.I)^j/(j.factorial : ℂ)).im

def error (x : ℝ) (n : ℕ) : ℝ := |x|^n/(n.factorial : ℝ)*2

theorem sine_error (x : ℝ) (n : ℕ) (hx : |x|/(n+1:ℕ) ≤ 1/2) :
    |Real.sin x-taylor x n| ≤ error x n := by
  have hnorm : ‖(x:ℂ)*Complex.I‖ = |x| := by simp
  have h := Complex.exp_bound' (x := (x:ℂ)*Complex.I) (n := n) (by simpa [hnorm] using hx)
  have hi := Complex.abs_im_le_norm
    (Complex.exp ((x:ℂ)*Complex.I) - ∑ j ∈ Finset.range n,
      ((x:ℂ)*Complex.I)^j/(j.factorial:ℂ))
  have hi' : |Real.sin x-taylor x n| ≤
      ‖Complex.exp ((x:ℂ)*Complex.I) - ∑ j ∈ Finset.range n,
        ((x:ℂ)*Complex.I)^j/(j.factorial:ℂ)‖ := by simpa [taylor] using hi
  exact hi'.trans (by simpa [hnorm,error] using h)

theorem sine_enclosure (x lo hi : ℝ) (n : ℕ) (hx : |x|/(n+1:ℕ) ≤ 1/2)
    (hl : lo ≤ taylor x n-error x n) (hu : taylor x n+error x n ≤ hi) :
    lo ≤ Real.sin x ∧ Real.sin x ≤ hi := by
  have h := abs_le.mp (sine_error x n hx)
  constructor <;> linarith

theorem perturbation_enclosure (x y lo hi radius : ℝ)
    (hy : lo ≤ Real.sin y ∧ Real.sin y ≤ hi) (hxy : |x-y| ≤ radius) :
    lo-radius ≤ Real.sin x ∧ Real.sin x ≤ hi+radius := by
  have h := abs_le.mp ((Real.abs_sin_sub_sin_le x y).trans hxy)
  constructor <;> linarith [hy.1,hy.2]

def piLo : ℝ := 314159265358979323846/100000000000000000000
def piHi : ℝ := 314159265358979323847/100000000000000000000

theorem pi_bounds : piLo ≤ Real.pi ∧ Real.pi ≤ piHi := by
  constructor
  · rw [show piLo = (3.14159265358979323846:ℝ) by norm_num [piLo]]
    exact Real.pi_gt_d20.le
  · rw [show piHi = (3.14159265358979323847:ℝ) by norm_num [piHi]]
    exact Real.pi_lt_d20.le

theorem pi_angle_error (r : ℝ) (hr : 0 ≤ r) :
    |Real.pi*r-piLo*r| ≤ (piHi-piLo)*r := by
  rw [← sub_mul,abs_of_nonneg (mul_nonneg (sub_nonneg.mpr pi_bounds.1) hr)]
  exact mul_le_mul_of_nonneg_right (sub_le_sub_right pi_bounds.2 _) hr

theorem pi_sine_enclosure (r lo hi : ℝ) (hr : 0 ≤ r)
    (h : lo ≤ Real.sin (piLo*r) ∧ Real.sin (piLo*r) ≤ hi) :
    lo-(piHi-piLo)*r ≤ Real.sin (Real.pi*r) ∧
      Real.sin (Real.pi*r) ≤ hi+(piHi-piLo)*r :=
  perturbation_enclosure _ _ _ _ _ h (pi_angle_error r hr)

def polynomial (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 11, (-1:ℝ)^j*x^(2*j+1)/((2*j+1).factorial:ℝ)

theorem taylor_real (x : ℝ) (n : ℕ) :
    taylor x n = ∑ j ∈ Finset.range n, x^j*(Complex.I^j).im/(j.factorial:ℝ) := by
  simp [taylor,mul_pow,← Complex.ofReal_pow,← Complex.ofReal_natCast,
    Complex.mul_im]

theorem taylor_23 (x : ℝ) : taylor x 23 = polynomial x := by
  rw [taylor_real]
  norm_num [polynomial,Finset.sum_range_succ,Complex.I_pow_eq_pow_mod,Nat.factorial]
  norm_num [Complex.I_sq,Complex.I_pow_three]

theorem polynomial_error (x : ℝ) (hx : |x| ≤ 2) :
    |Real.sin x-polynomial x| ≤ (2:ℝ)^24/(23:ℕ).factorial := by
  have h := sine_error x 23 (by norm_num; linarith)
  rw [taylor_23] at h
  apply h.trans
  unfold error
  have hp := pow_le_pow_left₀ (abs_nonneg x) hx 23
  norm_num [Nat.factorial] at hp ⊢
  nlinarith

def rationalPolynomial (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 11, (-1:ℚ)^j*x^(2*j+1)/((2*j+1).factorial:ℚ)

def rationalPiLo : ℚ := 314159265358979323846/100000000000000000000
def rationalPiHi : ℚ := 314159265358979323847/100000000000000000000
def rationalRadius (r : ℚ) : ℚ :=
  (2:ℚ)^24/(23:ℕ).factorial+(rationalPiHi-rationalPiLo)*r

def Checked (r lo hi : ℚ) : Prop :=
  0 ≤ r ∧ r ≤ 1/2 ∧
    lo ≤ rationalPolynomial (rationalPiLo*r)-rationalRadius r ∧
    rationalPolynomial (rationalPiLo*r)+rationalRadius r ≤ hi

instance (r lo hi : ℚ) : Decidable (Checked r lo hi) := inferInstanceAs
  (Decidable (0 ≤ r ∧ r ≤ 1/2 ∧
    lo ≤ rationalPolynomial (rationalPiLo*r)-rationalRadius r ∧
    rationalPolynomial (rationalPiLo*r)+rationalRadius r ≤ hi))

theorem cast_polynomial (x : ℚ) : (rationalPolynomial x:ℝ) = polynomial x := by
  simp [rationalPolynomial,polynomial]

theorem cast_pi_lo : (rationalPiLo:ℝ) = piLo := by norm_num [rationalPiLo,piLo]
theorem cast_pi_hi : (rationalPiHi:ℝ) = piHi := by norm_num [rationalPiHi,piHi]

theorem checked_sound (r lo hi : ℚ) (h : Checked r lo hi) :
    (lo:ℝ) ≤ Real.sin (Real.pi*(r:ℝ)) ∧ Real.sin (Real.pi*(r:ℝ)) ≤ (hi:ℝ) := by
  obtain ⟨hr,hrh,hl,hu⟩ := h
  have hr' : (0:ℝ) ≤ r := by exact_mod_cast hr
  have hrh' : (r:ℝ) ≤ 1/2 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hrh
    norm_num at hc
    exact hc
  have hp0 : 0 ≤ piLo := by norm_num [piLo]
  have hp4 : piLo ≤ 4 := by norm_num [piLo]
  have hx : |piLo*(r:ℝ)| ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg hp0 hr')]
    nlinarith
  have hs := polynomial_error (piLo*(r:ℝ)) hx
  have ht := Real.abs_sin_sub_sin_le (Real.pi*(r:ℝ)) (piLo*(r:ℝ))
  have htri := abs_add_le (Real.sin (Real.pi*(r:ℝ))-Real.sin (piLo*(r:ℝ)))
    (Real.sin (piLo*(r:ℝ))-polynomial (piLo*(r:ℝ)))
  have htotal : |Real.sin (Real.pi*(r:ℝ))-polynomial (piLo*(r:ℝ))| ≤
      (2:ℝ)^24/(23:ℕ).factorial+(piHi-piLo)*(r:ℝ) := by
    have hdiff := ht.trans (pi_angle_error r hr')
    rw [sub_add_sub_cancel] at htri
    linarith
  have hl' : (lo:ℝ) ≤ polynomial (piLo*(r:ℝ))-
      ((2:ℝ)^24/(23:ℕ).factorial+(piHi-piLo)*(r:ℝ)) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hl
    simpa [rationalRadius,cast_polynomial,cast_pi_lo,cast_pi_hi] using hc
  have hu' : polynomial (piLo*(r:ℝ))+
      ((2:ℝ)^24/(23:ℕ).factorial+(piHi-piLo)*(r:ℝ)) ≤ (hi:ℝ) := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hu
    simpa [rationalRadius,cast_polynomial,cast_pi_lo,cast_pi_hi] using hc
  have hab := abs_le.mp htotal
  constructor <;> linarith [hab.1,hab.2]

def fold (x : ℚ) : ℚ := |x-round x|

theorem fold_bounds (x : ℚ) : 0 ≤ fold x ∧ fold x ≤ 1/2 :=
  ⟨abs_nonneg _,abs_sub_round x⟩

theorem abs_sine_centered (x : ℝ) :
    |Real.sin (Real.pi*x)| = Real.sin (Real.pi*|x-round x|) := by
  have hr := abs_sub_round x
  have hx : |Real.pi*(x-round x)| ≤ Real.pi := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.abs_sin_eq_sin_abs_of_abs_le_pi hx
  rw [abs_mul,abs_of_pos Real.pi_pos] at h
  rw [show Real.pi*(x-round x) = Real.pi*x-(round x:ℝ)*Real.pi by ring,
    Real.sin_sub_int_mul_pi,abs_mul] at h
  simpa using h

theorem folded_sine (x : ℚ) :
    |Real.sin (Real.pi*(x:ℝ))| = Real.sin (Real.pi*(fold x:ℝ)) := by
  rw [abs_sine_centered]
  simp [fold,Rat.round_cast]

theorem checked_abs_sound (x lo hi : ℚ) (h : Checked (fold x) lo hi) :
    (lo:ℝ) ≤ |Real.sin (Real.pi*(x:ℝ))| ∧
      |Real.sin (Real.pi*(x:ℝ))| ≤ (hi:ℝ) := by
  rw [folded_sine]
  exact checked_sound _ _ _ h

end
end Borwein.SineCertificate
