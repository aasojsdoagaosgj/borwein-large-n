import Borwein.RadialVarianceLower

set_option autoImplicit false

namespace Borwein.VarianceInterval
noncomputable section
open RadialMoments GroupedWeights

def numerator (q : ℝ) : ℝ := q+4*q^2+10*q^3+20*q^4+10*q^5+4*q^6+q^7
def profile (q : ℝ) : ℝ := numerator q/denominator q^2

theorem numerator_nonneg (q : ℝ) (hq : 0 ≤ q) : 0 ≤ numerator q := by
  unfold numerator
  positivity

theorem numerator_mono (l u : ℝ) (hl : 0 ≤ l) (hlu : l ≤ u) : numerator l ≤ numerator u := by
  unfold numerator
  gcongr

theorem variance_eq_profile (y : ℝ) : variance y = profile (Real.exp (-y)) :=
  RadialVarianceLower.variance_formula y

theorem profile_enclosure (l q u : ℝ) (hl : 0 ≤ l) (hlq : l ≤ q) (hqu : q ≤ u) :
    numerator l/denominator u^2 ≤ profile q ∧ profile q ≤ numerator u/denominator l^2 := by
  have hq := hl.trans hlq
  have hu := hq.trans hqu
  have hdq := sq_pos_of_pos (denominator_pos q hq)
  have hdl := sq_pos_of_pos (denominator_pos l hl)
  have hdu := sq_pos_of_pos (denominator_pos u hu)
  have hdlq := pow_le_pow_left₀ (denominator_pos l hl).le (ExpCertificate.denominator_mono l q hl hlq) 2
  have hdqu := pow_le_pow_left₀ (denominator_pos q hq).le (ExpCertificate.denominator_mono q u hq hqu) 2
  unfold profile
  constructor
  · exact div_le_div₀ (numerator_nonneg q hq) (numerator_mono l q hl hlq) hdq hdqu
  · exact div_le_div₀ (numerator_nonneg u hu) (numerator_mono q u hq hqu) hdl hdlq

theorem rectangle_exp (A B τ a b x l u : ℝ) (hA : 0 ≤ A) (hAτ : A ≤ τ) (hτB : τ ≤ B)
    (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b)
    (hl : l ≤ Real.exp (-B*b)) (hu : Real.exp (-A*a) ≤ u) :
    l ≤ Real.exp (-(τ*x)) ∧ Real.exp (-(τ*x)) ≤ u := by
  have hτ := hA.trans hAτ
  have hB := hτ.trans hτB
  have hx := ha.trans hax
  have hlo := mul_le_mul hAτ hax ha hτ
  have hhi := mul_le_mul hτB hxb hx hB
  constructor
  · exact hl.trans (Real.exp_le_exp.mpr (by linarith))
  · exact (Real.exp_le_exp.mpr (by linarith)).trans hu

theorem rectangle_variance (A B τ a b x l u : ℝ) (hA : 0 ≤ A) (hAτ : A ≤ τ) (hτB : τ ≤ B)
    (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hl0 : 0 ≤ l)
    (hl : l ≤ Real.exp (-B*b)) (hu : Real.exp (-A*a) ≤ u) :
    numerator l/denominator u^2 ≤ variance (τ*x) ∧
      variance (τ*x) ≤ numerator u/denominator l^2 := by
  have h := rectangle_exp A B τ a b x l u hA hAτ hτB ha hax hxb hl hu
  rw [variance_eq_profile]
  exact profile_enclosure l _ u hl0 h.1 h.2

end
end Borwein.VarianceInterval
