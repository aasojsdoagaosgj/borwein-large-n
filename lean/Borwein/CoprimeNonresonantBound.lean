import Borwein.DivisibleNonresonantBound

set_option autoImplicit false

namespace Borwein.CoprimeNonresonantBound
noncomputable section
open FiniteBlockLocalization ResonantGeometricSum NonresonantGeometricBound
  DivisibleNonresonantBound

/-- This coarse two-frequency bound in fact holds without a coprimality hypothesis. -/
theorem nonresonant_bound (n Q K : ℕ) (τ θ η : ℝ) (q : ℚ)
    (hQ : 0 < Q) (hKQ : 5*K < Q) (hτ : 0 ≤ τ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hq : DirichletCover.Near (θ/(2*Real.pi)) Q q) :
    ‖ResonantFourierSplit.nonresonant n K (point n τ θ) η q‖ ≤
      ((q.den:ℝ)/(2*(1-(K:ℝ)/Q))+(q.den:ℝ)/(2*(1-5*(K:ℝ)/Q)))*Real.log (2/η) := by
  have hQ' : (0:ℝ) < Q := by exact_mod_cast hQ
  have hcut1 : 0 < 1-(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast (show K < Q by omega)))
  have hcut5 : 0 < 1-5*(K:ℝ)/Q := sub_pos.mpr ((div_lt_one hQ').mpr (by exact_mod_cast hKQ))
  have h1 := weighted_bound ((Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ k))
    (fun k => geometricSum (5*n) ((point n τ θ)^k)) η ((q.den:ℝ)/(2*(1-(K:ℝ)/Q)))
    hη hη1 (by positivity) (by
      intro k hk
      exact point_geometric_bound n (5*n) Q K k τ θ q hQ (by omega)
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2 hτ hq (Finset.mem_filter.mp hk).2)
  have h5 := weighted_bound ((Finset.Icc 1 K).filter (fun k => ¬ q.den ∣ 5*k))
    (fun k => geometricSum n ((point n τ θ)^(5*k))) η ((q.den:ℝ)/(2*(1-5*(K:ℝ)/Q)))
    hη hη1 (by positivity) (by
      intro k hk
      have hkK := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).2
      have h := point_geometric_bound n n Q (5*K) (5*k) τ θ q hQ hKQ
        (by omega) hτ hq (Finset.mem_filter.mp hk).2
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using h)
  unfold ResonantFourierSplit.nonresonant
  apply (norm_sub_le _ _).trans
  apply (add_le_add h1 h5).trans_eq
  ring

end
end Borwein.CoprimeNonresonantBound
