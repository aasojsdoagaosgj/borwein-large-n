import Borwein.GroupedWeights
import Borwein.StaircaseGap
import Borwein.LogKernel

namespace Borwein.ResonantCertificate
noncomputable section
open scoped BigOperators
open Borwein.PhaseGap Borwein.GroupedWeights Borwein.StaircaseGap Borwein.SincBounds

theorem integral_dominates_steps (f : ℝ → ℝ) (hf : Continuous f)
    (g b : ℕ → ℝ) (n : ℕ) (t : ℝ)
    (hgrid : ∀ i < n, b i ≤ b (i+1))
    (hcell : ∀ i < n, ∀ x ∈ Set.Icc (b i) (b (i+1)), g i ≤ f x) :
    (∑ i ∈ Finset.range n, g i * ∫ x in b i..b (i+1), (1-Real.cos (t*x))) ≤
      ∫ x in b 0..b n, f x*(1-Real.cos (t*x)) := by
  have hc : Continuous (fun x => f x*(1-Real.cos (t*x))) := by fun_prop
  rw [← intervalIntegral.sum_integral_adjacent_intervals
    (fun i (_ : i < n) => hc.intervalIntegrable (b i) (b (i+1)))]
  apply Finset.sum_le_sum
  intro i hi
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (hgrid i (Finset.mem_range.mp hi))
    ((show Continuous (fun x : ℝ => g i*(1-Real.cos (t*x))) by fun_prop).intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)
  intro x hx
  exact mul_le_mul_of_nonneg_right (hcell i (Finset.mem_range.mp hi) x hx)
    (sub_nonneg.mpr (Real.cos_le_one _))

def component (d : Fin 4) (τ t x : ℝ) :=
  groupedWeight (radialWeight (τ*x)) d * (1-Real.cos (((d:ℝ)+1)*t*x))

theorem continuous_component (d : Fin 4) (τ t : ℝ) : Continuous (component d τ t) := by
  have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (τ*x) j) := by fun_prop
  unfold component
  fin_cases d <;> simp only [groupedWeight] <;> fun_prop

def lowerSum (g b : ℕ → ℝ) (n : ℕ) (c : ℝ) :=
  ∑ i ∈ Finset.range n, (g i-g (i+1))*b (i+1)*profile (min 2 (c*b (i+1)))

theorem component_certificate (d : Fin 4) (τ t c : ℝ)
    (g b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 ≤ τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hg : g n = 0) (hb : b 0 = 0) (hend : b n = 1)
    (hgrid : ∀ i < n, b i ≤ b (i+1))
    (hpos : ∀ i ≤ n, 0 ≤ b i)
    (hdec : ∀ i < n, g (i+1) ≤ g i)
    (hbound : ∀ i < n, g i ≤ envelope d (τ*b (i+1))) :
    lowerSum g b n (((d:ℝ)+1)*c) ≤ ∫ x in (0:ℝ)..1, component d τ t x := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have ht' : ((d:ℝ)+1)*c ≤ |((d:ℝ)+1)*t| := by
    rw [abs_mul, abs_of_nonneg hd]
    exact mul_le_mul_of_nonneg_left ht hd
  have hs := staircase_lower g b n (((d:ℝ)+1)*t) (((d:ℝ)+1)*c) hg hb hdec
    (fun i hi => hpos (i+1) hi) (mul_nonneg hd hc) ht'
  have hf : Continuous (fun x => groupedWeight (radialWeight (τ*x)) d) := by
    have hp (j : Fin 5) : Continuous (fun x : ℝ => radialWeight (τ*x) j) := by fun_prop
    fin_cases d <;> simp only [groupedWeight] <;> fun_prop
  have hi := integral_dominates_steps _ hf g b n (((d:ℝ)+1)*t) hgrid (by
    intro i hin x hx
    apply le_trans (hbound i hin)
    simpa using staircase_cell_lower d 0 τ x (b (i+1)) (by norm_num) hτ
      (le_trans (hpos i (Nat.le_of_lt hin)) hx.1) hx.2)
  rw [hb, hend] at hi
  exact le_trans hs hi

theorem gapDensity_eq_sum (τ t x : ℝ) :
    gapDensity τ t x = ∑ d : Fin 4, component d τ t x := by
  simp [gapDensity, groupedGap, component, groupedWeight, Fin.sum_univ_four, mul_assoc]
  ring_nf


def certificate (g : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ) (c : ℝ) :=
  ∑ d : Fin 4, lowerSum (g d) b n (((d:ℝ)+1)*c)

theorem certificate_le_gap_integral (τ t c : ℝ)
    (g : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 ≤ τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hg : ∀ d, g d n = 0) (hb : b 0 = 0) (hend : b n = 1)
    (hgrid : ∀ i < n, b i ≤ b (i+1)) (hpos : ∀ i ≤ n, 0 ≤ b i)
    (hdec : ∀ d i, i < n → g d (i+1) ≤ g d i)
    (hbound : ∀ d i, i < n → g d i ≤ envelope d (τ*b (i+1))) :
    certificate g b n c ≤ ∫ x in (0:ℝ)..1, gapDensity τ t x := by
  simp_rw [gapDensity_eq_sum]
  rw [intervalIntegral.integral_finsetSum
    (fun d _ => (continuous_component d τ t).intervalIntegrable 0 1)]
  apply Finset.sum_le_sum
  intro d _
  exact component_certificate d τ t c (g d) b n hτ hc ht (hg d) hb hend
    hgrid hpos (hdec d) (hbound d)

theorem gap_integral_le_quadratic (τ t : ℝ) :
    (∫ x in (0:ℝ)..1, gapDensity τ t x) ≤
      ∫ x in (0:ℝ)..1, gapDensity τ t x + gapDensity τ t x^2 := by
  have h := continuous_gapDensity τ t
  apply intervalIntegral.integral_mono_on (by norm_num)
    (h.intervalIntegrable _ _) ((h.add (h.pow 2)).intervalIntegrable _ _)
  intro x _
  change gapDensity τ t x ≤ gapDensity τ t x + gapDensity τ t x ^ 2
  nlinarith [sq_nonneg (gapDensity τ t x)]

theorem certificate_le_phase_integral (τ t c : ℝ)
    (g : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 < τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hg : ∀ d, g d n = 0) (hb : b 0 = 0) (hend : b n = 1)
    (hgrid : ∀ i < n, b i ≤ b (i+1)) (hpos : ∀ i ≤ n, 0 ≤ b i)
    (hdec : ∀ d i, i < n → g d (i+1) ≤ g d i)
    (hbound : ∀ d i, i < n → g d i ≤ envelope d (τ*b (i+1))) :
    certificate g b n c ≤ ∫ x in (0:ℝ)..1, -Real.log ‖phase τ t x‖ :=
  le_trans (certificate_le_gap_integral τ t c g b n hτ.le hc ht hg hb hend hgrid hpos hdec hbound)
    (le_trans (gap_integral_le_quadratic τ t) (integral_phase_gap τ t hτ))

theorem certificate_le_kernelR_difference (τ t c : ℝ)
    (g : Fin 4 → ℕ → ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 < τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hg : ∀ d, g d n = 0) (hb : b 0 = 0) (hend : b n = 1)
    (hgrid : ∀ i < n, b i ≤ b (i+1)) (hpos : ∀ i ≤ n, 0 ≤ b i)
    (hdec : ∀ d i, i < n → g d (i+1) ≤ g d i)
    (hbound : ∀ d i, i < n → g d i ≤ envelope d (τ*b (i+1))) :
    certificate g b n c ≤ (Borwein.LogKernel.kernelR (τ:ℂ)).re -
      (Borwein.LogKernel.kernelR ((τ:ℂ)-(t:ℂ)*Complex.I)).re :=
  le_trans (certificate_le_gap_integral τ t c g b n hτ.le hc ht hg hb hend hgrid hpos hdec hbound)
    (le_trans (gap_integral_le_quadratic τ t)
      (Borwein.LogKernel.kernelR_re_difference_ge_quadratic τ t hτ))


theorem envelope_nonneg (d : Fin 4) (z : ℝ) : 0 ≤ envelope d z := by
  have hr (w : ℝ) : 0 ≤ radial d w := by
    rw [← groupedWeight_eq_radial]
    have hp (j : Fin 5) : 0 ≤ radialWeight w j := (radialWeight_pos w j).le
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    have h3 := hp 3
    have h4 := hp 4
    fin_cases d <;> norm_num [groupedWeight] <;> positivity
  exact le_min (hr 0) (hr z)

def heights (b : ℕ → ℝ) (n : ℕ) (τ : ℝ) (d : Fin 4) (i : ℕ) :=
  if i < n then envelope d (τ*b (i+1)) else 0

theorem heights_last (b : ℕ → ℝ) (n : ℕ) (τ : ℝ) (d : Fin 4) :
    heights b n τ d n = 0 := by simp [heights]

theorem heights_decreasing (b : ℕ → ℝ) (n : ℕ) (τ : ℝ)
    (hτ : 0 ≤ τ) (hb : b 0 = 0) (hm : Monotone b) (d : Fin 4) (i : ℕ) (hi : i < n) :
    heights b n τ d (i+1) ≤ heights b n τ d i := by
  have hp (k : ℕ) : 0 ≤ b k := by simpa [hb] using hm (Nat.zero_le k)
  rw [heights, heights, if_pos hi]
  split_ifs with hn
  · apply antitoneOn_envelope d (mul_nonneg hτ (hp _)) (mul_nonneg hτ (hp _))
    exact mul_le_mul_of_nonneg_left (hm (Nat.le_succ _)) hτ
  · exact envelope_nonneg d _

theorem canonical_certificate_le_kernelR (τ t c : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 < τ) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hb : b 0 = 0) (hend : b n = 1) (hm : Monotone b) :
    certificate (heights b n τ) b n c ≤ (Borwein.LogKernel.kernelR (τ:ℂ)).re -
      (Borwein.LogKernel.kernelR ((τ:ℂ)-(t:ℂ)*Complex.I)).re := by
  apply certificate_le_kernelR_difference τ t c (heights b n τ) b n hτ hc ht
    (heights_last b n τ) hb hend
  · exact fun i _ => hm (Nat.le_succ i)
  · intro i _
    simpa [hb] using hm (Nat.zero_le i)
  · exact heights_decreasing b n τ hτ.le hb hm
  · intro d i hi
    simp [heights, hi]


theorem uniform_certificate_le_kernelR (τ T t c : ℝ) (b : ℕ → ℝ) (n : ℕ)
    (hτ : 0 < τ) (hT : τ ≤ T) (hc : 0 ≤ c) (ht : c ≤ |t|)
    (hb : b 0 = 0) (hend : b n = 1) (hm : Monotone b) :
    certificate (heights b n T) b n c ≤ (Borwein.LogKernel.kernelR (τ:ℂ)).re -
      (Borwein.LogKernel.kernelR ((τ:ℂ)-(t:ℂ)*Complex.I)).re := by
  have hp (i : ℕ) : 0 ≤ b i := by simpa [hb] using hm (Nat.zero_le i)
  have hT0 := le_trans hτ.le hT
  apply certificate_le_kernelR_difference τ t c (heights b n T) b n hτ hc ht
    (heights_last b n T) hb hend
  · exact fun i _ => hm (Nat.le_succ i)
  · exact fun i _ => hp i
  · exact heights_decreasing b n T hT0 hb hm
  · intro d i hi
    simp only [heights, if_pos hi]
    exact antitoneOn_envelope d (mul_nonneg hτ.le (hp _)) (mul_nonneg hT0 (hp _))
      (mul_le_mul_of_nonneg_right hT (hp _))

def uniformGrid (n : ℕ) (i : ℕ) : ℝ := (i:ℝ)/(n:ℝ)

theorem uniformGrid_monotone (n : ℕ) : Monotone (uniformGrid n) := by
  intro i j hij
  apply div_le_div_of_nonneg_right (by exact_mod_cast hij)
  positivity

theorem uniform_grid_certificate (τ T t c : ℝ) (n : ℕ)
    (hn : 0 < n) (hτ : 0 < τ) (hT : τ ≤ T) (hc : 0 ≤ c) (ht : c ≤ |t|) :
    certificate (heights (uniformGrid n) n T) (uniformGrid n) n c ≤
      (Borwein.LogKernel.kernelR (τ:ℂ)).re -
      (Borwein.LogKernel.kernelR ((τ:ℂ)-(t:ℂ)*Complex.I)).re :=
  uniform_certificate_le_kernelR τ T t c (uniformGrid n) n hτ hT hc ht
    (by simp [uniformGrid]) (by simp [uniformGrid, Nat.ne_of_gt hn]) (uniformGrid_monotone n)

end
end Borwein.ResonantCertificate
