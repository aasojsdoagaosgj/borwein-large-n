import Borwein.EndpointGMinor

set_option autoImplicit false

namespace Borwein.CertifiedEndpointSign
noncomputable section
open EndpointCoefficientConnection PhaseIntegral

theorem strong_sign_of_cutoff (a : Fin 3) (n m : ℕ) (hn : 0 < n) (hm : 155734 ≤ m)
    (ha : m%5=a.val) (hband : (m:ℝ)/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2)) :
    0 < EndpointStrongConstants.sigma a*((Borwein.polynomial n).coeff m:ℝ) :=
  EndpointRangeSign.strong_sign_of_cutoff a n m hn hm ha hband EndpointGMinor.GMinorBound

theorem weak_sign_of_cutoff (a n m : ℕ) (hn : 0 < n) (hk : 155734 ≤ shiftedIndex n m)
    (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hband : shiftedIndex n m/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2)) :
    (Borwein.polynomial n).coeff m < 0 :=
  EndpointRangeSign.weak_sign_of_cutoff a n m hn hk ha hA hband EndpointGMinor.GMinorBound

theorem global_strong_sign (a : Fin 3) (n m : ℕ) (hn : 31147 ≤ n) (hm : 5*n ≤ m)
    (ha : m%5=a.val) (hband : (m:ℝ)/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2)) :
    0 < EndpointStrongConstants.sigma a*((Borwein.polynomial n).coeff m:ℝ) :=
  EndpointRangeSign.global_strong_sign a n m hn hm ha hband EndpointGMinor.GMinorBound

theorem global_weak_sign (a n m : ℕ) (hn : 31147 ≤ n) (hm : 10*n ≤ m)
    (ha : m%5=a) (hA : a=3 ∨ a=4)
    (hband : shiftedIndex n m/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2)) :
    (Borwein.polynomial n).coeff m < 0 :=
  EndpointRangeSign.global_weak_sign a n m hn hm ha hA hband EndpointGMinor.GMinorBound

end
end Borwein.CertifiedEndpointSign
