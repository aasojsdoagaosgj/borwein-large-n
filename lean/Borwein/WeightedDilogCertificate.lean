import Borwein.DenominatorOnePositiveCertificate

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Borwein.WeightedDilogCertificate
noncomputable section
open PositiveCuspCertificate

theorem exp_double : Real.exp (-(2*eta)) ≤ 4911/5000 := by
  apply (ExpCertificate.exp_enclosure _ 0 (4911/5000) 12 (by norm_num [eta]) (by norm_num) ?_ ?_).2
  all_goals norm_num [eta,ExpCertificate.taylorSum,ExpCertificate.remainder,Finset.sum_range_succ,Nat.factorial]

theorem radial_double : DilogarithmUpper.radial (2*eta) ≤ 39/25 := by
  apply (DilogarithmTail.radial_upper (2*eta) (4911/5000) (by norm_num [eta]) exp_double (by norm_num)).trans
  apply (DilogarithmTail.series_upper 60 (4911/5000) (by norm_num) (by norm_num)).trans
  norm_num [Finset.sum_range_succ]

end
end Borwein.WeightedDilogCertificate
