import Borwein.DirichletCover
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

namespace Borwein.AngularKernel
noncomputable section

theorem sine_distance (x : ℝ) :
    2*|x-round x| ≤ |Real.sin (Real.pi*x)| := by
  have hr := abs_sub_round x
  have hx : |Real.pi*(x-round x)| ≤ Real.pi/2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have h := Real.mul_abs_le_abs_sin hx
  have he : Real.pi*(x-round x) = Real.pi*x-(round x:ℝ)*Real.pi := by ring
  rw [he, Real.sin_sub_int_mul_pi, abs_mul] at h
  have ha : |(-1:ℝ)^(round x)| = 1 := by simp
  rw [ha, one_mul] at h
  have hab : |Real.pi*x-(round x:ℝ)*Real.pi| = Real.pi*|x-round x| := by
    rw [← he, abs_mul, abs_of_pos Real.pi_pos]
  rw [hab] at h
  have hc : (2/Real.pi)*(Real.pi*|x-round x|) = 2*|x-round x| := by
    field_simp
  rwa [hc] at h

theorem residue_sine_lower (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (k : ℕ) :
    2*(DirichletCover.residue q k-(k:ℝ)/Q)/(q.den:ℝ) ≤
      |Real.sin (Real.pi*((k:ℝ)*ξ))| := by
  have hd := DirichletCover.residue_distance_lower ξ Q hQ q h k
    (round ((k:ℝ)*ξ))
  have hs := sine_distance ((k:ℝ)*ξ)
  have hh := (mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 2)).trans hs
  simpa only [mul_div_assoc] using hh

def circle (u : ℝ) : ℂ := (Real.cos u:ℂ)+(Real.sin u:ℂ)*Complex.I

theorem radial_distance_sq (ρ u : ℝ) :
    ‖1-(ρ:ℂ)*circle u‖^2 = (1-ρ)^2+4*ρ*(Real.sin (u/2))^2 := by
  have hc := Real.cos_two_mul (u/2)
  have hs := Real.sin_sq_add_cos_sq (u/2)
  rw [show 2*(u/2)=u by ring] at hc
  have hu := Real.sin_sq_add_cos_sq u
  have hu' := congrArg (fun v : ℝ => ρ^2*v) hu
  have hc' : Real.cos u = 1-2*(Real.sin (u/2))^2 := by linarith
  have hc'' := congrArg (fun v : ℝ => ρ*v) hc'
  simp only [Complex.sq_norm, Complex.normSq_apply, circle,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith

theorem radial_distance_lower (ρ u : ℝ) (hρ : 0 ≤ ρ) :
    2*Real.sqrt ρ*|Real.sin (u/2)| ≤ ‖1-(ρ:ℂ)*circle u‖ := by
  have he := radial_distance_sq ρ u
  have hs := Real.sq_sqrt hρ
  have ha := sq_abs (Real.sin (u/2))
  have hsq : (2*Real.sqrt ρ*|Real.sin (u/2)|)^2 ≤ ‖1-(ρ:ℂ)*circle u‖^2 := by
    calc
      _ = 4*ρ*(Real.sin (u/2))^2 := by nlinarith [sq_nonneg (Real.sqrt ρ)]
      _ ≤ _ := by nlinarith [sq_nonneg (1-ρ)]
  nlinarith [norm_nonneg (1-(ρ:ℂ)*circle u),
    show 0 ≤ 2*Real.sqrt ρ*|Real.sin (u/2)| by positivity]

theorem circle_eq_exp (u : ℝ) : circle u = Complex.exp ((u:ℂ)*Complex.I) := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rfl

theorem circle_pow (u : ℝ) (k : ℕ) : (circle u)^k = circle ((k:ℝ)*u) := by
  rw [circle_eq_exp, ← Complex.exp_nat_mul, circle_eq_exp]
  congr 1
  push_cast
  ring

theorem circle_norm (u : ℝ) : ‖circle u‖ = 1 := by
  rw [circle_eq_exp, Complex.norm_exp]
  simp

theorem radial_pow (ρ u : ℝ) (k : ℕ) :
    ((ρ:ℂ)*circle u)^k = ((ρ^k:ℝ):ℂ)*circle ((k:ℝ)*u) := by
  rw [mul_pow, circle_pow, Complex.ofReal_pow]

theorem radial_factor_ne_zero (ρ u : ℝ) (hρ : 0 < ρ)
    (hu : Real.sin (u/2) ≠ 0) : 1-(ρ:ℂ)*circle u ≠ 0 := by
  apply norm_pos_iff.mp
  exact lt_of_lt_of_le (by positivity) (radial_distance_lower ρ u hρ.le)

theorem denominator_product_lower (ρ u : ℝ) (hρ : 0 ≤ ρ) :
    4*ρ^3*|Real.sin (u/2)| *|Real.sin (5*u/2)| ≤
      ‖1-(ρ:ℂ)*circle u‖*‖1-((ρ:ℂ)*circle u)^5‖ := by
  have h1 := radial_distance_lower ρ u hρ
  have h5 := radial_distance_lower (ρ^5) (5*u) (pow_nonneg hρ _)
  have hprod := mul_le_mul h1 h5 (by positivity) (norm_nonneg _)
  have hs : Real.sqrt ρ*Real.sqrt (ρ^5) = ρ^3 := by
    rw [← Real.sqrt_mul hρ, show ρ*ρ^5 = (ρ^3)^2 by ring,
      Real.sqrt_sq (pow_nonneg hρ _)]
  rw [radial_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _ = (2*Real.sqrt ρ*|Real.sin (u/2)|)*
        (2*Real.sqrt (ρ^5)*|Real.sin (5*u/2)|) := by
      calc
        _ = 4*(Real.sqrt ρ*Real.sqrt (ρ^5))*|Real.sin (u/2)| *
            |Real.sin (5*u/2)| := by rw [hs]
        _ = _ := by ring
    _ ≤ _ := hprod

theorem radial_kernel_upper (ρ u : ℝ) (hρ : 0 < ρ)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.kernel ((ρ:ℂ)*circle u)‖ ≤
      ‖1-((ρ:ℂ)*circle u)^4‖ /
        (4*ρ^2*|Real.sin (u/2)| *|Real.sin (5*u/2)|) := by
  have hd := denominator_product_lower ρ u hρ.le
  have hp : 0 < 4*ρ^3*|Real.sin (u/2)| *|Real.sin (5*u/2)| := by positivity
  unfold FiniteFourierKernel.kernel
  rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hρ.le, circle_norm, mul_one]
  have hh := div_le_div_of_nonneg_left
    (show 0 ≤ ρ*‖1-((ρ:ℂ)*circle u)^4‖ by positivity) hp hd
  refine hh.trans_eq ?_
  field_simp

theorem radial_finiteSum_upper (n : ℕ) (ρ u : ℝ) (hρ : 0 < ρ)
    (hu : Real.sin (u/2) ≠ 0) (h5u : Real.sin (5*u/2) ≠ 0) :
    ‖FiniteFourierKernel.finiteSum n ((ρ:ℂ)*circle u)‖ ≤
      (1+ρ^(5*n))*(‖1-((ρ:ℂ)*circle u)^4‖ /
        (4*ρ^2*|Real.sin (u/2)| * |Real.sin (5*u/2)|)) := by
  have hz : (ρ:ℂ)*circle u ≠ 1 :=
    (sub_ne_zero.mp (radial_factor_ne_zero ρ u hρ hu)).symm
  have hz5 : ((ρ:ℂ)*circle u)^5 ≠ 1 := by
    rw [radial_pow]
    norm_num only [Nat.cast_ofNat]
    exact (sub_ne_zero.mp (radial_factor_ne_zero (ρ^5) (5*u)
      (pow_pos hρ _) h5u)).symm
  have h := FiniteFourierKernel.norm_exact_block n ((ρ:ℂ)*circle u) hz hz5
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le, circle_norm, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (radial_kernel_upper ρ u hρ hu h5u)
    (by positivity))

theorem near_radial_factor_lower (ρ ξ : ℝ) (hρ : 0 ≤ ρ)
    (Q : ℕ) (hQ : 0 < Q) (q : ℚ) (h : DirichletCover.Near ξ Q q) (k : ℕ) :
    4*Real.sqrt ρ*(DirichletCover.residue q k-(k:ℝ)/Q)/(q.den:ℝ) ≤
      ‖1-(ρ:ℂ)*circle (2*Real.pi*((k:ℝ)*ξ))‖ := by
  have hs := residue_sine_lower ξ Q hQ q h k
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : (0:ℝ) ≤ 2*Real.sqrt ρ)
  have hd := radial_distance_lower ρ (2*Real.pi*((k:ℝ)*ξ)) hρ
  rw [show 2*Real.pi*((k:ℝ)*ξ)/2 = Real.pi*((k:ℝ)*ξ) by ring] at hd
  have he : 4*Real.sqrt ρ*(DirichletCover.residue q k-(k:ℝ)/Q)/(q.den:ℝ) =
      (2*Real.sqrt ρ)*(2*(DirichletCover.residue q k-(k:ℝ)/Q)/(q.den:ℝ)) := by ring
  rw [he]
  exact hm.trans hd

end
end Borwein.AngularKernel

