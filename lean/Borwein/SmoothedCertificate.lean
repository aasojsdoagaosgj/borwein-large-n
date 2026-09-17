import Borwein.SmoothedPhase

namespace Borwein.SmoothedCertificate
noncomputable section
open scoped BigOperators
open Borwein.PhaseGap Borwein.PhaseIntegral Borwein.GroupedWeights
open Borwein.StaircaseGap Borwein.SincBounds Borwein.ResonantCertificate Borwein.SmoothedPhase

def component (d : Fin 4) (η τ t x : ℝ) :=
  groupedWeight (radialWeight (η+τ*x)) d * (1-Real.cos (((d:ℝ)+1)*t*x))

theorem continuous_component (d : Fin 4) (η τ t : ℝ) : Continuous (component d η τ t) := by
  have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (η+τ*x) j) := by fun_prop
  unfold component
  fin_cases d <;> simp only [groupedWeight] <;> fun_prop

theorem component_certificate (d : Fin 4) (η τ t c : ℝ)
    (g b : ℕ → ℝ) (n : ℕ)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hg : g n = 0) (hb : b 0 = 0) (hend : b n = 1)
    (hgrid : ∀ i < n, b i ≤ b (i+1))
    (hpos : ∀ i ≤ n, 0 ≤ b i)
    (hdec : ∀ i < n, g (i+1) ≤ g i)
    (hbound : ∀ i < n, g i ≤ envelope d (η+τ*b (i+1))) :
    lowerSum g b n (((d:ℝ)+1)*c) ≤ ∫ x in (0:ℝ)..1, component d η τ t x := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have ht' : ((d:ℝ)+1)*c ≤ |((d:ℝ)+1)*t| := by
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left ht hd
  have hs := staircase_lower g b n (((d:ℝ)+1)*t) (((d:ℝ)+1)*c) hg hb hdec
    (fun i hi => hpos (i+1) hi) (mul_nonneg hd hc) ht'
  have hf : Continuous (fun x => groupedWeight (radialWeight (η+τ*x)) d) := by
    have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (η+τ*x) j) := by fun_prop
    fin_cases d <;> simp only [groupedWeight] <;> fun_prop
  have hi := integral_dominates_steps _ hf g b n (((d:ℝ)+1)*t) hgrid (by
    intro i hin x hx
    apply le_trans (hbound i hin)
    simpa using staircase_cell_lower d η τ x (b (i+1)) hη hτ
      (le_trans (hpos i (Nat.le_of_lt hin)) hx.1) hx.2)
  rw [hb, hend] at hi
  exact le_trans hs hi

theorem gapDensity_eq_sum (η τ t x : ℝ) :
    smoothedGap η τ t x = ∑ d : Fin 4, component d η τ t x := by
  simp [smoothedGap, groupedGap, component, groupedWeight, Fin.sum_univ_four, mul_assoc]
  ring_nf


theorem certificate_le_gap_integral (η τ t c : ℝ)
    (g : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hg : ∀ d, g d n = 0) (hb : b 0 = 0) (hend : b n = 1)
    (hgrid : ∀ i < n, b i ≤ b (i+1)) (hpos : ∀ i ≤ n, 0 ≤ b i)
    (hdec : ∀ d i, i < n → g d (i+1) ≤ g d i)
    (hbound : ∀ d i, i < n → g d i ≤ envelope d (η+τ*b (i+1))) :
    certificate g b n c ≤ ∫ x in (0:ℝ)..1, smoothedGap η τ t x := by
  simp_rw [gapDensity_eq_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun d _ => (continuous_component d η τ t).intervalIntegrable 0 1)]
  apply Finset.sum_le_sum
  intro d _
  exact component_certificate d η τ t c (g d) b n hη hτ hc ht (hg d) hb hend
    hgrid hpos (hdec d) (hbound d)



def shiftedHeights (b : ℕ → ℝ) (n : ℕ) (η T : ℝ) (d : Fin 4) (i : ℕ) :=
  if i < n then envelope d (η+T*b (i+1)) else 0

theorem shiftedHeights_last (b : ℕ → ℝ) (n : ℕ) (η T : ℝ) (d : Fin 4) :
    shiftedHeights b n η T d n = 0 := by simp [shiftedHeights]

theorem shiftedHeights_decreasing (b : ℕ → ℝ) (n : ℕ) (η T : ℝ)
    (hη : 0 ≤ η) (hT : 0 ≤ T) (hb : b 0 = 0) (hm : Monotone b)
    (d : Fin 4) (i : ℕ) (hi : i < n) :
    shiftedHeights b n η T d (i+1) ≤ shiftedHeights b n η T d i := by
  have hp (k : ℕ) : 0 ≤ b k := by simpa [hb] using hm (Nat.zero_le k)
  rw [shiftedHeights, shiftedHeights, if_pos hi]
  split_ifs with hn
  · apply antitoneOn_envelope d
      (add_nonneg hη (mul_nonneg hT (hp _))) (add_nonneg hη (mul_nonneg hT (hp _)))
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hm (Nat.le_succ _)) hT)
  · exact envelope_nonneg d _

theorem uniform_shifted_lower (η τ T t c : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hT : τ ≤ T) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hb : b 0 = 0) (hend : b n = 1) (hm : Monotone b) :
    certificate (shiftedHeights b n η T) b n c ≤
      ∫ x in (0:ℝ)..1, smoothedGap η τ t x := by
  have hp (k : ℕ) : 0 ≤ b k := by simpa [hb] using hm (Nat.zero_le k)
  have hT0 := le_trans hτ hT
  apply certificate_le_gap_integral η τ t c (shiftedHeights b n η T) b n hη hτ hc ht
    (shiftedHeights_last b n η T) hb hend
  · exact fun i _ => hm (Nat.le_succ i)
  · exact fun i _ => hp i
  · exact shiftedHeights_decreasing b n η T hη hT0 hb hm
  · intro d i hi
    simp only [shiftedHeights, if_pos hi]
    exact antitoneOn_envelope d
      (add_nonneg hη (mul_nonneg hτ (hp _))) (add_nonneg hη (mul_nonneg hT0 (hp _)))
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hT (hp _)))

theorem uniform_shifted_modulus_upper (η τ T t c : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hT : τ ≤ T) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hb : b 0 = 0) (hend : b n = 1) (hm : Monotone b) :
    smoothedModulus η τ t ≤ radialR τ-certificate (shiftedHeights b n η T) b n c := by
  have h := uniform_shifted_lower η τ T t c b n hη hτ hT hc ht hb hend hm
  have hi : (∫ x in (0:ℝ)..1, smoothedGap η τ t x) ≤
      ∫ x in (0:ℝ)..1, smoothedGap η τ t x+smoothedGap η τ t x^2 := by
    have hc := continuous_smoothedGap η τ t
    apply intervalIntegral.integral_mono_on (by norm_num)
      (hc.intervalIntegrable _ _) ((hc.add (hc.pow 2)).intervalIntegrable _ _)
    intro x _
    change smoothedGap η τ t x ≤ smoothedGap η τ t x+smoothedGap η τ t x^2
    nlinarith [sq_nonneg (smoothedGap η τ t x)]
  have hu := smoothedModulus_upper η τ t hη hτ
  linarith

def uniformGap (η T c : ℝ) (n : ℕ) :=
  certificate (shiftedHeights (uniformGrid n) n η T) (uniformGrid n) n c

theorem uniform_grid_modulus_upper (η τ T t c : ℝ) (n : ℕ)
    (hn : 0 < n) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hT : τ ≤ T) (hc : 0 ≤ c) (ht : c ≤ |t|) :
    smoothedModulus η τ t ≤ radialR τ-uniformGap η T c n :=
  uniform_shifted_modulus_upper η τ T t c (uniformGrid n) n hη hτ hT hc ht
    (by simp [uniformGrid]) (by simp [uniformGrid, Nat.ne_of_gt hn]) (uniformGrid_monotone n)

theorem radial_at_zero (d : Fin 4) : radial d 0 = (4-(d:ℝ))/25 := by
  fin_cases d <;> norm_num [radial, weight, numerator, denominator]

theorem height_matches_code (η T : ℝ) (n i : ℕ) (d : Fin 4) (hi : i < n) :
    shiftedHeights (uniformGrid n) n η T d i =
      min ((4-(d:ℝ))/25)
        (weight d (Real.exp (-(η+T*((i+1:ℕ):ℝ)/(n:ℝ))))) := by
  simp only [shiftedHeights, if_pos hi, envelope]
  rw [radial_at_zero]
  simp only [radial, uniformGrid, mul_div_assoc]

/-- Analytic consequence at the current Python parameters; the numerical gap remains unevaluated. -/
theorem current_parameters_upper (τ t : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ 11/2)
    (ht : 6/5 ≤ |t|) :
    smoothedModulus (113/40000) τ t ≤ radialR τ-uniformGap (113/40000) (11/2) (6/5) 400 :=
  uniform_grid_modulus_upper _ _ _ _ _ _ (by norm_num) (by norm_num) hτ hT (by norm_num) ht

end
end Borwein.SmoothedCertificate
