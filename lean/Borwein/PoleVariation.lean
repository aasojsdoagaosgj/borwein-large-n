import Borwein.RadialKernelProfile

namespace Borwein.PoleVariation
noncomputable section
open AngularKernel

theorem circle_add (u v : ℝ) : circle (u+v) = circle u*circle v := by
  simp only [circle_eq_exp, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem circle_lipschitz (u v : ℝ) : ‖circle u-circle v‖ ≤ |u-v| := by
  have he : circle u-circle v = circle v*(circle (u-v)-1) := by
    have h := circle_add v (u-v)
    rw [show v+(u-v)=u by ring] at h
    rw [h]
    ring
  rw [he, norm_mul, circle_norm, one_mul, norm_sub_rev,
    RadialKernelProfile.unit_distance]
  have h := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := (u-v)/2))
    (by norm_num : (0:ℝ) ≤ 2)
  simpa only [abs_div, abs_of_pos (by norm_num : (0:ℝ)<2), mul_div_cancel₀ _ (by norm_num : (2:ℝ)≠0)] using h

def pole (u : ℝ) : ℂ := (1-circle u)⁻¹

theorem pole_difference (u v : ℝ) (hu : 1-circle u ≠ 0) (hv : 1-circle v ≠ 0) :
    ‖pole u-pole v‖ ≤ |u-v|/(‖1-circle u‖*‖1-circle v‖) := by
  have he : pole u-pole v = (circle u-circle v)/((1-circle u)*(1-circle v)) := by
    unfold pole
    field_simp
    ring
  rw [he, norm_div, norm_mul]
  exact div_le_div_of_nonneg_right (circle_lipschitz u v) (by positivity)

theorem chord_distance_lower (x : ℝ) :
    4*|x-round x| ≤ ‖1-circle (2*Real.pi*x)‖ := by
  rw [RadialKernelProfile.unit_distance, show 2*Real.pi*x/2=Real.pi*x by ring]
  nlinarith [AngularKernel.sine_distance x]

theorem pole_bound_of_distances (x y s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hx : s ≤ |x-round x|) (hy : t ≤ |y-round y|) :
    ‖pole (2*Real.pi*x)-pole (2*Real.pi*y)‖ ≤
      Real.pi*|x-y|/(8*s*t) := by
  have hx' : 4*s ≤ ‖1-circle (2*Real.pi*x)‖ := by
    linarith [chord_distance_lower x]
  have hy' : 4*t ≤ ‖1-circle (2*Real.pi*y)‖ := by
    linarith [chord_distance_lower y]
  have hxn := norm_pos_iff.mp (show 0 < ‖1-circle (2*Real.pi*x)‖ by linarith)
  have hyn := norm_pos_iff.mp (show 0 < ‖1-circle (2*Real.pi*y)‖ by linarith)
  have h := pole_difference (2*Real.pi*x) (2*Real.pi*y) hxn hyn
  have hd := mul_le_mul hx' hy' (by positivity) (norm_nonneg _)
  have hh := div_le_div_of_nonneg_left (abs_nonneg (2*Real.pi*x-2*Real.pi*y))
    (show 0 < (4*s)*(4*t) by positivity) hd
  refine h.trans (hh.trans_eq ?_)
  rw [show 2*Real.pi*x-2*Real.pi*y = (2*Real.pi)*(x-y) by ring,
    abs_mul, abs_of_pos (by positivity : 0 < 2*Real.pi)]
  field_simp
  ring

theorem near_pole_variation (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (k : ℕ)
    (hr : (k:ℝ)/Q < DirichletCover.residue q k) :
    ‖pole (2*Real.pi*((k:ℝ)*q))-pole (2*Real.pi*((k:ℝ)*ξ))‖ ≤
      Real.pi*q.den*k /
        (8*Q*DirichletCover.residue q k*(DirichletCover.residue q k-(k:ℝ)/Q)) := by
  have hb : (0:ℝ) < q.den := Nat.cast_pos.mpr q.pos
  have hQ' : (0:ℝ) < Q := Nat.cast_pos.mpr hQ
  have hr0 : 0 < DirichletCover.residue q k :=
    lt_of_le_of_lt (div_nonneg (Nat.cast_nonneg k) hQ'.le) hr
  have hp : 0 < DirichletCover.residue q k-(k:ℝ)/Q := sub_pos.mpr hr
  have hs := pole_bound_of_distances ((k:ℝ)*q) ((k:ℝ)*ξ)
    (DirichletCover.residue q k/q.den)
    ((DirichletCover.residue q k-(k:ℝ)/Q)/q.den)
    (div_pos hr0 hb) (div_pos hp hb)
    (DirichletCover.residue_minimal q k (round ((k:ℝ)*q)))
    (DirichletCover.residue_distance_lower ξ Q hQ q h k (round ((k:ℝ)*ξ)))
  have he := DirichletCover.scaled_error ξ Q q h k
  rw [abs_sub_comm ((k:ℝ)*ξ) ((k:ℝ)*q)] at he
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left he Real.pi_pos.le)
    (show 0 ≤ 8*(DirichletCover.residue q k/q.den)*
      ((DirichletCover.residue q k-(k:ℝ)/Q)/q.den) by positivity)
  refine hs.trans (hm.trans_eq ?_)
  field_simp

theorem near_pole_variation_nonresonant (ξ : ℝ) (Q : ℕ) (hQ : 0 < Q)
    (q : ℚ) (h : DirichletCover.Near ξ Q q) (k : ℕ)
    (hk : ¬ q.den ∣ k) (hkQ : k < Q) :
    ‖pole (2*Real.pi*((k:ℝ)*q))-pole (2*Real.pi*((k:ℝ)*ξ))‖ ≤
      Real.pi*q.den*k /
        (8*Q*DirichletCover.residue q k*(DirichletCover.residue q k-(k:ℝ)/Q)) := by
  apply near_pole_variation ξ Q hQ q h k
  have hf : (k:ℝ)/Q < 1 := (div_lt_one (Nat.cast_pos.mpr hQ)).mpr
    (by exact_mod_cast hkQ)
  exact hf.trans_le (DirichletCover.residue_ge_one q k hk)

theorem weighted_denominator_bound (A r k K Q w : ℝ)
    (hA : 0 ≤ A) (hr : 1 ≤ r) (hk : 0 ≤ k) (hkK : k ≤ K)
    (hKQ : K < Q) (hwk : w*k ≤ 1) :
    w*(A*k/(r*(r-k/Q))) ≤ A/((1-K/Q)*r^2) := by
  have hQ : 0 < Q := lt_of_le_of_lt (hk.trans hkK) hKQ
  have hK : 0 ≤ K/Q := div_nonneg (hk.trans hkK) hQ.le
  have hcut : 0 < 1-K/Q := sub_pos.mpr ((div_lt_one hQ).mpr hKQ)
  have hr0 : 0 < r := by linarith
  have hmul : K/Q ≤ r*(K/Q) := by nlinarith [mul_nonneg (sub_nonneg.mpr hr) hK]
  have hkk : k/Q ≤ K/Q := div_le_div_of_nonneg_right hkK hQ.le
  have hlow : r*(1-K/Q) ≤ r-k/Q := by nlinarith
  have hd : (1-K/Q)*r^2 ≤ r*(r-k/Q) := by
    nlinarith [mul_le_mul_of_nonneg_left hlow hr0.le]
  have hd0 : 0 < (1-K/Q)*r^2 := by positivity
  have hd1 : 0 < r*(r-k/Q) := hd0.trans_le hd
  calc
    _ = A*(w*k)/(r*(r-k/Q)) := by ring
    _ ≤ A/(r*(r-k/Q)) := by
      apply div_le_div_of_nonneg_right _ hd1.le
      nlinarith [mul_le_mul_of_nonneg_left hwk hA]
    _ ≤ _ := div_le_div_of_nonneg_left hA hd0 hd

theorem fourier_weight_cancellation (η : ℝ) (hη : 0 ≤ η) (k : ℕ) (hk : 0 < k) :
    (Real.exp (-η*k)/(k:ℝ))*(k:ℝ) ≤ 1 := by
  rw [div_mul_cancel₀ _ (by exact_mod_cast hk.ne')]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη) (Nat.cast_nonneg k))

end
end Borwein.PoleVariation
