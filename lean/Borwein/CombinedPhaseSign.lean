import Borwein.PhaseAngleRange

set_option autoImplicit false

namespace Borwein.CombinedPhaseSign
noncomputable section
open ExplicitPhaseProfile PhaseAngleRange

def sign (a : ℕ) : ℝ := if a = 0 then 1 else -1

theorem cosine_product_sign (a : ℕ) (ha : a < 5) (u v : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u < Real.pi/10) (hv0 : 0 ≤ v) (hv1 : v < Real.pi/10) :
    0 < sign a*(4*Real.cos (3*Real.pi*(a:ℝ)/5+u)*Real.cos (-Real.pi*(a:ℝ)/5+v)) := by
  have hp := Real.pi_pos
  interval_cases a
  · have hcu := Real.cos_pos_of_mem_Ioo (x := u) ⟨by linarith,by linarith⟩
    have hcv := Real.cos_pos_of_mem_Ioo (x := v) ⟨by linarith,by linarith⟩
    norm_num [sign]
    positivity
  · have hca : Real.cos (3*Real.pi*(1:ℝ)/5+u) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    have hcb : 0 < Real.cos (-Real.pi*(1:ℝ)/5+v) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
    have hm := mul_neg_of_neg_of_pos hca hcb
    norm_num only [sign,ite_false,Nat.cast_one]
    nlinarith
  · have hca : Real.cos (3*Real.pi*(2:ℝ)/5+u) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    have hcb : 0 < Real.cos (-Real.pi*(2:ℝ)/5+v) :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
    have hm := mul_neg_of_neg_of_pos hca hcb
    norm_num only [sign,ite_false,Nat.cast_ofNat]
    nlinarith
  · have hca : 0 < Real.cos (3*Real.pi*(3:ℝ)/5+u) := by
      have he : 3*Real.pi*(3:ℝ)/5+u = (3*Real.pi*(3:ℝ)/5+u-2*Real.pi)+2*Real.pi := by ring
      rw [he,Real.cos_add_two_pi]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
    have hcb : Real.cos (-Real.pi*(3:ℝ)/5+v) < 0 := by
      rw [← Real.cos_neg (-Real.pi*(3:ℝ)/5+v)]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    have hm := mul_neg_of_pos_of_neg hca hcb
    norm_num only [sign,ite_false,Nat.cast_ofNat]
    nlinarith
  · have hca : 0 < Real.cos (3*Real.pi*(4:ℝ)/5+u) := by
      have he : 3*Real.pi*(4:ℝ)/5+u = (3*Real.pi*(4:ℝ)/5+u-2*Real.pi)+2*Real.pi := by ring
      rw [he,Real.cos_add_two_pi]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith,by linarith⟩
    have hcb : Real.cos (-Real.pi*(4:ℝ)/5+v) < 0 := by
      rw [← Real.cos_neg (-Real.pi*(4:ℝ)/5+v)]
      exact Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    have hm := mul_neg_of_pos_of_neg hca hcb
    norm_num only [sign,ite_false,Nat.cast_ofNat]
    nlinarith

theorem signed_phase_pos (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    0 < sign a*phase a τ := by
  have h := angle_ranges τ hτ
  exact cosine_product_sign a ha _ _ h.1.1 h.1.2 h.2.1 h.2.2

theorem abs_phase_eq_signed (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    |phase a τ| = sign a*phase a τ := by
  have hp := signed_phase_pos a ha τ hτ
  by_cases h : a = 0
  · simp only [sign,if_pos h,one_mul] at hp ⊢
    exact abs_of_pos hp
  · simp only [sign,if_neg h,neg_one_mul] at hp ⊢
    exact abs_of_neg (by linarith)

theorem signed_psi_real_pos (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    0 < sign a*(CombinedAmplitude.psi FivePoleCircle.zeta a (τ:ℂ)).re := by
  rw [psi_eq_profile a ha τ hτ,Complex.ofReal_re]
  exact signed_phase_pos a ha τ hτ

theorem psi_norm_eq_signed (a : ℕ) (ha : a < 5) (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖CombinedAmplitude.psi FivePoleCircle.zeta a (τ:ℂ)‖ = sign a*phase a τ := by
  rw [profile_norm a ha τ hτ,abs_phase_eq_signed a ha τ hτ]

theorem weak_three_identity (τ : ℝ) :
    -phase 3 τ = 4*Real.cos (Real.pi/5-(alpha τ+2*beta τ)/5)*
      Real.sin (Real.pi/10-(2*alpha τ-beta τ)/5) := by
  unfold phase
  norm_num only [Nat.cast_ofNat]
  have he1 : 3*Real.pi*(3:ℝ)/5+(alpha τ+2*beta τ)/5 =
      2*Real.pi-(Real.pi/5-(alpha τ+2*beta τ)/5) := by ring
  have he2 : -Real.pi*(3:ℝ)/5+(2*alpha τ-beta τ)/5 =
      -(Real.pi/2+(Real.pi/10-(2*alpha τ-beta τ)/5)) := by ring
  rw [he1,he2,Real.cos_two_pi_sub,Real.cos_neg,Real.cos_add,Real.cos_pi_div_two,Real.sin_pi_div_two]
  ring

theorem weak_four_identity (τ : ℝ) :
    -phase 4 τ = 4*Real.sin (Real.pi/10-(alpha τ+2*beta τ)/5)*
      Real.cos (Real.pi/5+(2*alpha τ-beta τ)/5) := by
  unfold phase
  norm_num only [Nat.cast_ofNat]
  have he1 : 3*Real.pi*(4:ℝ)/5+(alpha τ+2*beta τ)/5 =
      (Real.pi/2-(Real.pi/10-(alpha τ+2*beta τ)/5))+2*Real.pi := by ring
  have he2 : -Real.pi*(4:ℝ)/5+(2*alpha τ-beta τ)/5 =
      (Real.pi/5+(2*alpha τ-beta τ)/5)-Real.pi := by ring
  rw [he1,he2,Real.cos_add_two_pi,Real.cos_pi_div_two_sub,Real.cos_sub_pi]
  ring

end
end Borwein.CombinedPhaseSign
