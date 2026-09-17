import Borwein.EndpointSaddleRange

set_option autoImplicit false

namespace Borwein.EndpointRangeSign
noncomputable section
open EndpointSaddleRange EndpointCoefficientConnection EndpointOuterTransfer PhaseIntegral

/-- Endpoint signs in the original coefficient variables; no saddle radius is supplied by the caller. -/
theorem strong_sign_of_cutoff (a : Fin 3) (n m : ℕ) (hn : 0 < n) (hm : 155734 ≤ m)
    (ha : m%5=a.val) (hband : (m:ℝ)/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2))
    (hG : ∀ v : ℝ, 0 < v → v ≤ 13/10000 → GMinorBound v) :
    0 < EndpointStrongConstants.sigma a*((Borwein.polynomial n).coeff m:ℝ) := by
  obtain ⟨v,hv,hV,hτ,hs⟩ := exists_small_endpoint_saddle n (m:ℝ) hn (by exact_mod_cast hm) hband
  exact EndpointConditionalSign.strong_sign a n m v hn hv hV hτ ha hs (hG v hv hV)

/-- The shifted cutoff applies uniformly in n to the actual weak coefficient. -/
theorem weak_sign_of_cutoff (a n m : ℕ) (hn : 0 < n) (hk : 155734 ≤ shiftedIndex n m)
    (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hband : shiftedIndex n m/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2))
    (hG : ∀ v : ℝ, 0 < v → v ≤ 13/10000 → GMinorBound v) :
    (Borwein.polynomial n).coeff m < 0 := by
  obtain ⟨v,hv,hV,hτ,hs⟩ := exists_small_endpoint_saddle n (shiftedIndex n m) hn hk hband
  exact EndpointWeakIntegralZero.weak_sign a n m v hn hv hV hτ ha hA hs (hG v hv hV)

theorem global_strong_sign (a : Fin 3) (n m : ℕ) (hn : 31147 ≤ n) (hm : 5*n ≤ m)
    (ha : m%5=a.val) (hband : (m:ℝ)/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2))
    (hG : ∀ v : ℝ, 0 < v → v ≤ 13/10000 → GMinorBound v) :
    0 < EndpointStrongConstants.sigma a*((Borwein.polynomial n).coeff m:ℝ) :=
  strong_sign_of_cutoff a n m (by omega) (by omega) ha hband hG

theorem global_weak_sign (a n m : ℕ) (hn : 31147 ≤ n) (hm : 10*n ≤ m)
    (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hband : shiftedIndex n m/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2))
    (hG : ∀ v : ℝ, 0 < v → v ≤ 13/10000 → GMinorBound v) :
    (Borwein.polynomial n).coeff m < 0 := by
  have hnR : (31147:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hmR : 10*(n:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hk : 155734 ≤ shiftedIndex n m := by unfold shiftedIndex; push_cast; linarith
  exact weak_sign_of_cutoff a n m (by omega) hk ha hA hband hG

end
end Borwein.EndpointRangeSign
