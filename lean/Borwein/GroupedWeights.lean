import Borwein.PhaseGap
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Borwein.GroupedWeights
noncomputable section
open Borwein.PhaseGap

def denominator (y : ℝ) := 1+y+y^2+y^3+y^4
def numerator (d : Fin 4) (y : ℝ) : ℝ :=
  ![y+y^3+y^5+y^7, y^2+y^4+y^6, y^3+y^5, y^4] d
def qPoly (d : Fin 4) (y : ℝ) : ℝ :=
  ![1-4*y^3-7*y^4-7*y^5-4*y^6+y^9,
    2*y+2*y^2+4*y^3+2*y^4+2*y^5+4*y^6+2*y^7+2*y^8,
    3*y^2+4*y^3+8*y^4+8*y^5+4*y^6+3*y^7,
    4*y^3+6*y^4+6*y^5+4*y^6] d
def weight (d : Fin 4) (y : ℝ) := numerator d y / denominator y ^ 2

theorem denominator_pos (y : ℝ) (hy : 0 ≤ y) : 0 < denominator y := by
  unfold denominator
  positivity

theorem hasDerivAt_weight (d : Fin 4) (y : ℝ) (hy : denominator y ≠ 0) :
    HasDerivAt (weight d) ((1-y)*qPoly d y / denominator y^3) y := by
  have hd := ((((hasDerivAt_const y (1:ℝ)).add (hasDerivAt_id y)).add
    ((hasDerivAt_id y).pow 2)).add ((hasDerivAt_id y).pow 3)).add
      ((hasDerivAt_id y).pow 4)
  change HasDerivAt denominator _ y at hd
  fin_cases d
  · have h := ((((hasDerivAt_id y).add ((hasDerivAt_id y).pow 3)).add ((hasDerivAt_id y).pow 5)).add ((hasDerivAt_id y).pow 7)).div (hd.pow 2) (pow_ne_zero 2 hy)
    change HasDerivAt (weight 0) _ y at h
    apply h.congr_deriv
    norm_num [qPoly, denominator, id_eq]
    have hn : 1+y+y^2+y^3+y^4 ≠ 0 := hy
    field_simp
    ring
  · have h := ((((hasDerivAt_id y).pow 2).add ((hasDerivAt_id y).pow 4)).add ((hasDerivAt_id y).pow 6)).div (hd.pow 2) (pow_ne_zero 2 hy)
    change HasDerivAt (weight 1) _ y at h
    apply h.congr_deriv
    norm_num [qPoly, denominator, id_eq]
    have hn : 1+y+y^2+y^3+y^4 ≠ 0 := hy
    field_simp
    ring
  · have h := (((hasDerivAt_id y).pow 3).add ((hasDerivAt_id y).pow 5)).div (hd.pow 2) (pow_ne_zero 2 hy)
    change HasDerivAt (weight 2) _ y at h
    apply h.congr_deriv
    norm_num [qPoly, denominator, id_eq]
    have hn : 1+y+y^2+y^3+y^4 ≠ 0 := hy
    field_simp
    ring
  · have h := ((hasDerivAt_id y).pow 4).div (hd.pow 2) (pow_ne_zero 2 hy)
    change HasDerivAt (weight 3) _ y at h
    apply h.congr_deriv
    norm_num [qPoly, denominator, id_eq]
    have hn : 1+y+y^2+y^3+y^4 ≠ 0 := hy
    field_simp
    ring


theorem qPoly_nonneg (d : Fin 4) (hd : d ≠ 0) (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ qPoly d y := by
  fin_cases d
  · exact False.elim (hd rfl)
  all_goals norm_num [qPoly]; positivity

theorem monotoneOn_weight (d : Fin 4) (hd : d ≠ 0) :
    MonotoneOn (weight d) (Set.Icc 0 1) := by
  have hh (y : ℝ) (hy : y ∈ Set.Icc (0:ℝ) 1) :=
    hasDerivAt_weight d y (ne_of_gt (denominator_pos y hy.1))
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact fun y hy => (hh y hy).continuousAt.continuousWithinAt
  · exact fun y hy => (hh y (interior_subset hy)).differentiableAt.differentiableWithinAt
  · intro y hy
    have h := interior_subset hy
    rw [(hh y h).deriv]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr h.2) (qPoly_nonneg d hd y h.1))
      (le_of_lt (pow_pos (denominator_pos y h.1) 3))

def radial (d : Fin 4) (z : ℝ) := weight d (Real.exp (-z))

theorem antitoneOn_radial (d : Fin 4) (hd : d ≠ 0) :
    AntitoneOn (radial d) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply monotoneOn_weight d hd
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)⟩
  · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)⟩
  · exact Real.exp_le_exp.mpr (neg_le_neg hxy)

def groupedWeight (p : Fin 5 → ℝ) (d : Fin 4) : ℝ :=
  ![p 0*p 1+p 1*p 2+p 2*p 3+p 3*p 4,
    p 0*p 2+p 1*p 3+p 2*p 4, p 0*p 3+p 1*p 4, p 0*p 4] d

theorem radialWeight_eq_power (z : ℝ) (j : Fin 5) :
    radialWeight z j = Real.exp (-z)^(j:ℕ) / denominator (Real.exp (-z)) := by
  have he (k : Fin 5) : Real.exp (-(k:ℝ)*z) = Real.exp (-z)^(k:ℕ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  unfold radialWeight
  simp_rw [he]
  simp [Fin.sum_univ_five, denominator]

theorem groupedWeight_eq_radial (d : Fin 4) (z : ℝ) :
    groupedWeight (radialWeight z) d = radial d z := by
  have hn := ne_of_gt (denominator_pos (Real.exp (-z)) (Real.exp_pos _).le)
  fin_cases d <;> simp [groupedWeight, radial, weight, numerator, radialWeight_eq_power]
  all_goals field_simp

theorem groupedWeight_lower (d : Fin 4) (hd : d ≠ 0) (z B : ℝ)
    (hz : 0 ≤ z) (hB : z ≤ B) :
    radial d B ≤ groupedWeight (radialWeight z) d := by
  rw [groupedWeight_eq_radial]
  exact antitoneOn_radial d hd hz (le_trans hz hB) hB


theorem hasDerivAt_qZero (y : ℝ) :
    HasDerivAt (qPoly 0) (-12*y^2-28*y^3-35*y^4-24*y^5+9*y^8) y := by
  have h := (((((hasDerivAt_const y (1:ℝ)).sub (((hasDerivAt_id y).pow 3).const_mul 4)).sub
    (((hasDerivAt_id y).pow 4).const_mul 7)).sub
    (((hasDerivAt_id y).pow 5).const_mul 7)).sub
    (((hasDerivAt_id y).pow 6).const_mul 4)).add ((hasDerivAt_id y).pow 9)
  change HasDerivAt (qPoly 0) _ y at h
  apply h.congr_deriv
  simp only [id_eq]
  ring

theorem antitoneOn_qZero : AntitoneOn (qPoly 0) (Set.Icc 0 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
  · exact fun y _ => (hasDerivAt_qZero y).continuousAt.continuousWithinAt
  · exact fun y _ => (hasDerivAt_qZero y).differentiableAt.differentiableWithinAt
  · intro y hy
    have h : y ∈ Set.Icc (0:ℝ) 1 := interior_subset hy
    rw [(hasDerivAt_qZero y).deriv]
    have hp : y^8 ≤ y^2 := pow_le_pow_of_le_one h.1 h.2 (by norm_num)
    have h3 : 0 ≤ y^3 := pow_nonneg h.1 _
    have h4 : 0 ≤ y^4 := pow_nonneg h.1 _
    have h5 : 0 ≤ y^5 := pow_nonneg h.1 _
    nlinarith [sq_nonneg y]

theorem weight_zero_endpoint_lower (A y B : ℝ)
    (hA : 0 ≤ A) (hAy : A ≤ y) (hyB : y ≤ B) (hB : B ≤ 1) :
    min (weight 0 A) (weight 0 B) ≤ weight 0 y := by
  have hI (x : ℝ) (hx : x ∈ Set.Icc A B) : x ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans hA hx.1, le_trans hx.2 hB⟩
  have hd (x : ℝ) (hx : x ∈ Set.Icc A B) :=
    hasDerivAt_weight 0 x (ne_of_gt (denominator_pos x (hI x hx).1))
  by_cases hq : 0 ≤ qPoly 0 y
  · have hm : MonotoneOn (weight 0) (Set.Icc A y) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc A y)
      · intro x hx
        exact (hd x ⟨hx.1, le_trans hx.2 hyB⟩).continuousAt.continuousWithinAt
      · intro x hx
        have hh := interior_subset hx
        exact (hd x ⟨hh.1, le_trans hh.2 hyB⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        have hh := interior_subset hx
        have hi := hI x ⟨hh.1, le_trans hh.2 hyB⟩
        rw [(hd x ⟨hh.1, le_trans hh.2 hyB⟩).deriv]
        have hqx := antitoneOn_qZero hi (hI y ⟨hAy,hyB⟩) hh.2
        exact div_nonneg (mul_nonneg (sub_nonneg.mpr hi.2) (le_trans hq hqx))
          (le_of_lt (pow_pos (denominator_pos x hi.1) 3))
    exact le_trans (min_le_left _ _) (hm ⟨le_rfl,hAy⟩ ⟨hAy,le_rfl⟩ hAy)
  · have hm : AntitoneOn (weight 0) (Set.Icc y B) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc y B)
      · intro x hx
        exact (hd x ⟨le_trans hAy hx.1,hx.2⟩).continuousAt.continuousWithinAt
      · intro x hx
        have hh := interior_subset hx
        exact (hd x ⟨le_trans hAy hh.1,hh.2⟩).differentiableAt.differentiableWithinAt
      · intro x hx
        have hh := interior_subset hx
        have hi := hI x ⟨le_trans hAy hh.1,hh.2⟩
        rw [(hd x ⟨le_trans hAy hh.1,hh.2⟩).deriv]
        have hqx := antitoneOn_qZero (hI y ⟨hAy,hyB⟩) hi hh.1
        exact div_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hi.2)
            (le_trans hqx (le_of_not_ge hq)))
          (le_of_lt (pow_pos (denominator_pos x hi.1) 3))
    exact le_trans (min_le_right _ _) (hm ⟨le_rfl,hyB⟩ ⟨hyB,le_rfl⟩ hyB)

theorem radial_endpoint_lower (d : Fin 4) (A z B : ℝ)
    (hA : 0 ≤ A) (hAz : A ≤ z) (hzB : z ≤ B) :
    min (radial d A) (radial d B) ≤ groupedWeight (radialWeight z) d := by
  rw [groupedWeight_eq_radial]
  by_cases hd : d = 0
  · subst d
    rw [min_comm]
    exact weight_zero_endpoint_lower _ _ _ (Real.exp_pos _).le
      (Real.exp_le_exp.mpr (neg_le_neg hzB))
      (Real.exp_le_exp.mpr (neg_le_neg hAz))
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hA))
  · exact le_trans (min_le_right _ _)
      (antitoneOn_radial d hd (le_trans hA hAz) (le_trans hA (le_trans hAz hzB)) hzB)


def envelope (d : Fin 4) (z : ℝ) := min (radial d 0) (radial d z)

theorem antitoneOn_envelope (d : Fin 4) :
    AntitoneOn (envelope d) (Set.Ici 0) := by
  intro A hA B hB hAB
  apply le_min (min_le_left _ _)
  have h := radial_endpoint_lower d 0 A B (by norm_num) hA hAB
  rw [groupedWeight_eq_radial] at h
  exact h

theorem envelope_lower (d : Fin 4) (z B : ℝ) (hz : 0 ≤ z) (hB : z ≤ B) :
    envelope d B ≤ groupedWeight (radialWeight z) d :=
  radial_endpoint_lower d 0 z B (by norm_num) hz hB

theorem staircase_cell_lower (d : Fin 4) (η τ x b : ℝ)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hx : 0 ≤ x) (hxb : x ≤ b) :
    envelope d (η+τ*b) ≤ groupedWeight (radialWeight (η+τ*x)) d :=
  envelope_lower d _ _ (by positivity) (add_le_add le_rfl (mul_le_mul_of_nonneg_left hxb hτ))

end
end Borwein.GroupedWeights




