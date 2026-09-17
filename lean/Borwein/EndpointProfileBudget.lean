import Borwein.EndpointProfileMonotone

set_option autoImplicit false

namespace Borwein.EndpointProfileBudget
noncomputable section
open EndpointPhaseDerivatives EndpointScaledBounds EndpointProfileMonotone

def tail (T : ℝ) (k : ℕ) : ℝ := if k=0 then 0 else Real.exp (-T*(k:ℝ))
def weightTail (T : ℝ) (k : ℕ) : ℝ := (k:ℝ)*Real.exp (-T*(k:ℝ))
def quadratic (T : ℝ) : ℝ := 1+T+T^2/2
def B2 (T : ℝ) : ℝ := (8/5)*quadratic T*Real.exp (-T)/(1-Real.exp (-T))
def B3 (T : ℝ) : ℝ := (24/5)*(quadratic T*Real.exp (-T)/(1-Real.exp (-T))+
  T^3/6*Real.exp (-T)/(1-Real.exp (-T))^2)

theorem exp_frequency (T : ℝ) (k : ℕ) : Real.exp (-T*(k:ℝ))=Real.exp (-T)^k := by
  rw [mul_comm, Real.exp_nat_mul]

theorem tail_hasSum (T : ℝ) (hT : 0 < T) :
    HasSum (tail T) (Real.exp (-T)/(1-Real.exp (-T))) := by
  have hr : |Real.exp (-T)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hh := (hasSum_geometric_of_abs_lt_one hr).mul_left (Real.exp (-T))
  apply (hasSum_nat_add_iff' 1).mp
  simp only [tail, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false,
    Finset.sum_range_one, if_true, sub_zero]
  convert! hh using 1
  funext k
  rw [show -T*((k+1:ℕ):ℝ)=(-T)*(k:ℝ)+(-T) by push_cast; ring,
    Real.exp_add, exp_frequency]
  ring

theorem weightTail_hasSum (T : ℝ) (hT : 0 < T) :
    HasSum (weightTail T) (Real.exp (-T)/(1-Real.exp (-T))^2) := by
  have hr : ‖Real.exp (-T)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  exact (hasSum_coe_mul_geometric_of_norm_lt_one hr).congr_fun (fun k => by rw [weightTail, exp_frequency])

theorem second_term_bound (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    secondProfile T k ≤ (8/5)*quadratic T*tail T k := by
  by_cases hk : k=0
  · simp [hk, secondProfile, tail]
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hsq : (k:ℝ) ≤ (k:ℝ)^2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hsq hT
  have hb : (1+T*(k:ℝ)+(T*(k:ℝ))^2/2)/(k:ℝ)^2 ≤ quadratic T := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^2)).mpr
    unfold quadratic
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ (8/5)*Real.exp (-T*(k:ℝ)))
  simp only [secondProfile, tail, if_neg hk]
  convert! hh using 1 <;> ring

theorem third_term_bound (T : ℝ) (hT : 0 ≤ T) (k : ℕ) :
    thirdProfile T k ≤ (24/5)*(quadratic T*tail T k+(T^3/6)*weightTail T k) := by
  by_cases hk : k=0
  · simp [hk, thirdProfile, tail, weightTail]
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hsq : (k:ℝ) ≤ (k:ℝ)^2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_left hsq hT
  have hb : (1+T*(k:ℝ)+(T*(k:ℝ))^2/2+(T*(k:ℝ))^3/6)/(k:ℝ)^2 ≤ quadratic T+(T^3/6)*(k:ℝ) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (k:ℝ)^2)).mpr
    unfold quadratic
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ (24/5)*Real.exp (-T*(k:ℝ)))
  simp only [thirdProfile, tail, if_neg hk, weightTail]
  convert! hh using 1 <;> ring

theorem second_envelope_hasSum (T : ℝ) (hT : 0 < T) :
    HasSum (fun k => (8/5)*quadratic T*tail T k) (B2 T) := by
  convert! (tail_hasSum T hT).mul_left ((8/5)*quadratic T) using 1
  unfold B2
  ring

theorem third_envelope_hasSum (T : ℝ) (hT : 0 < T) :
    HasSum (fun k => (24/5)*(quadratic T*tail T k+(T^3/6)*weightTail T k)) (B3 T) := by
  convert! (((tail_hasSum T hT).mul_left (quadratic T)).add
    ((weightTail_hasSum T hT).mul_left (T^3/6))).mul_left (24/5) using 1
  unfold B3
  ring

theorem uniform_second_bound (n : ℕ) (v y T : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hT : 0 < T) (hτ : T ≤ ((5*n:ℕ):ℝ)*v) : v^3*‖q2 n v y‖ ≤ B2 T := by
  apply (second_bound n v y hn hv).trans
  have hh := (second_hasSum n v hn hv).summable.tsum_le_tsum
    (fun k => (second_antitone T _ hT.le hτ k).trans (second_term_bound T hT.le k))
    (second_envelope_hasSum T hT).summable
  simpa only [(second_envelope_hasSum T hT).tsum_eq] using hh

theorem uniform_third_bound (n : ℕ) (v y T : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hT : 0 < T) (hτ : T ≤ ((5*n:ℕ):ℝ)*v) : v^4*‖q3 n v y‖ ≤ B3 T := by
  apply (third_bound n v y hn hv).trans
  have hh := (third_hasSum n v hn hv).summable.tsum_le_tsum
    (fun k => (third_antitone T _ hT.le hτ k).trans (third_term_bound T hT.le k))
    (third_envelope_hasSum T hT).summable
  simpa only [(third_envelope_hasSum T hT).tsum_eq] using hh

end
end Borwein.EndpointProfileBudget
