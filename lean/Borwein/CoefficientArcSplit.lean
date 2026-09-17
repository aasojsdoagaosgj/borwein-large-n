import Borwein.SaddleArcConnection

namespace Borwein.CoefficientArcSplit
noncomputable section
open Complex Set MeasureTheory CoefficientIntegral SaddleArcConnection

def gapSum (n m : ℕ) (τ h : ℝ) : ℂ :=
  (∫ u in (0:ℝ)..center 0-h/(5*n), angular (Borwein.polynomial n) m (radius n τ) u)+
  (∫ u in center 0+h/(5*n)..center 1-h/(5*n), angular (Borwein.polynomial n) m (radius n τ) u)+
  (∫ u in center 1+h/(5*n)..center 2-h/(5*n), angular (Borwein.polynomial n) m (radius n τ) u)+
  (∫ u in center 2+h/(5*n)..center 3-h/(5*n), angular (Borwein.polynomial n) m (radius n τ) u)+
  (∫ u in center 3+h/(5*n)..2*Real.pi, angular (Borwein.polynomial n) m (radius n τ) u)

def minorContribution (n m : ℕ) (τ h : ℝ) : ℂ :=
  gapSum n m τ h/((radius n τ:ℂ)^m*(2*Real.pi:ℂ))

theorem interval_difference (f : ℝ → ℂ) (hf : Continuous f) (a b : ℝ) :
    (∫ t in a..b, f t) = (∫ t in (0:ℝ)..b, f t)-(∫ t in (0:ℝ)..a, f t) :=
  (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable 0 b) (hf.intervalIntegrable 0 a)).symm

theorem four_arc_partition (f : ℝ → ℂ) (hf : Continuous f) (T a1 b1 a2 b2 a3 b3 a4 b4 : ℝ) :
    (∫ t in (0:ℝ)..T, f t) =
      ((∫ t in a1..b1, f t)+(∫ t in a2..b2, f t)+(∫ t in a3..b3, f t)+(∫ t in a4..b4, f t))+
      ((∫ t in (0:ℝ)..a1, f t)+(∫ t in b1..a2, f t)+(∫ t in b2..a3, f t)+
        (∫ t in b3..a4, f t)+(∫ t in b4..T, f t)) := by
  rw [interval_difference f hf a1 b1,interval_difference f hf a2 b2,
    interval_difference f hf a3 b3,interval_difference f hf a4 b4,
    interval_difference f hf b1 a2,interval_difference f hf b2 a3,
    interval_difference f hf b3 a4,interval_difference f hf b4 T]
  ring

theorem angular_partition (n m : ℕ) (τ h : ℝ) :
    (∫ t in (0:ℝ)..2*Real.pi, angular (Borwein.polynomial n) m (radius n τ) t) =
      arcSum n m τ h+gapSum n m τ h := by
  have he := four_arc_partition (angular (Borwein.polynomial n) m (radius n τ))
    (angular_continuous _ _ _) (2*Real.pi)
    (center 0-h/(5*n)) (center 0+h/(5*n))
    (center 1-h/(5*n)) (center 1+h/(5*n))
    (center 2-h/(5*n)) (center 2+h/(5*n))
    (center 3-h/(5*n)) (center 3+h/(5*n))
  unfold arcSum gapSum
  norm_num [Fin.sum_univ_succ,SaddleArcConnection.center,add_assoc] at he ⊢
  exact he

theorem coefficient_split (n m : ℕ) (τ h : ℝ) :
    ((Borwein.polynomial n).coeff m:ℂ) = majorContribution n m τ h+minorContribution n m τ h := by
  have hr : 0 < radius n τ := Real.exp_pos _
  rw [borwein_coefficient_formula n m (radius n τ) hr,angular_partition]
  unfold majorContribution minorContribution
  rw [add_div]

theorem normalized_coefficient_error (n m : ℕ) (τ h N : ℝ)
    (hN : 0 < N) (hn : N ≤ n) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 11/2)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 2/5)
    (hs : -RadialDerivatives.firstDerivative τ = (m:ℝ)/(5*(n:ℝ)^2)) :
    ‖((Borwein.polynomial n).coeff m:ℂ)/(bulkScale n m τ:ℂ)-
      CombinedAmplitude.psi FivePoleCircle.zeta (m%5) (τ:ℂ)‖ ≤
    FiniteMajorArc.normalizedError FivePoleCircle.zeta (m%5) n τ h N+
      ‖minorContribution n m τ h‖/bulkScale n m τ := by
  have hnNat : 0 < n := by exact_mod_cast hN.trans_le hn
  have hB := bulkScale_pos n m τ hnNat
  have he := major_contribution_error n m τ h N hN hn hτ0 hτ1 hh0 hh1 hs
  rw [coefficient_split,add_div]
  have htri (A B C : ℂ) : ‖A+B-C‖ ≤ ‖A-C‖+‖B‖ := by
    have hx : A+B-C = (A-C)+B := by ring
    rw [hx]
    exact norm_add_le _ _
  apply (htri _ _ _).trans
  apply add_le_add he
  rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hB.le]

end
end Borwein.CoefficientArcSplit
