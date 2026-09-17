import Borwein.EndpointRadialSign

set_option autoImplicit false

namespace Borwein.EndpointSaddleRange
noncomputable section
open Complex EndpointActualPhase EndpointSaddleIdentification EndpointRadialSign
  PhaseIntegral RadialDerivatives SaddlePoint

/-- Manuscript endpoint radius estimate, before any small-radius or large-tau assumption. -/
theorem saddle_radius (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) : k*v^2 ≤ A := by
  have hi := congrArg Complex.re (first_identification n v hn hv)
  rw [Complex.ofReal_re, firstModel, ← deriv_radialR] at hi
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hD : 5*(n:ℝ)^2 ≠ 0 := by positivity
  have hs' := (eq_div_iff hD).mp hs
  have he : -(f1 n v 0).re=k := by nlinarith
  have hu := first_main_upper n v hn hv
  rw [he] at hu
  exact (le_div_iff₀ (by positivity : 0 < v^2)).mp hu

theorem radius_constant : A < (155734:ℝ)*(13/10000)^2 := by
  have hh := mul_self_lt_mul_self Real.pi_pos.le Real.pi_lt_d6
  unfold A
  nlinarith

theorem saddle_radius_small (n : ℕ) (k v : ℝ) (hn : 0 < n) (hv : 0 < v)
    (hk : 155734 ≤ k) (hs : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2)) :
    v ≤ 13/10000 := by
  have hh := saddle_radius n k v hn hv hs
  have hl := mul_le_mul_of_nonneg_right hk (sq_nonneg v)
  have hA := radius_constant
  nlinarith

theorem boundary_ratio : 0 < -deriv radialR (11/2) ∧ -deriv radialR (11/2) < 1 := by
  rw [deriv_radialR]
  have h0 := firstDerivative_neg (11/2)
  have h1 := strictMono_firstDerivative (show (0:ℝ) < 11/2 by norm_num)
  rw [firstDerivative_zero] at h1
  constructor <;> linarith

/-- Every endpoint ratio has a saddle on the endpoint side of the joining point. -/
theorem exists_endpoint_saddle (r : ℝ) (hr : 0 < r) (hR : r ≤ -deriv radialR (11/2)) :
    ∃ τ : ℝ, 11/2 ≤ τ ∧ -deriv radialR τ=r := by
  obtain ⟨τ,⟨hτ0,hs⟩,_⟩ := existsUnique_positive_saddle r hr (hR.trans_lt boundary_ratio.2)
  refine ⟨τ,?_,hs⟩
  by_contra h
  have hh := strictMono_firstDerivative (lt_of_not_ge h)
  rw [deriv_radialR] at hs hR
  linarith

/-- The fixed coefficient cutoff 155734 suffices for every positive n. -/
theorem exists_small_endpoint_saddle (n : ℕ) (k : ℝ) (hn : 0 < n) (hk : 155734 ≤ k)
    (hband : k/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2)) :
    ∃ v : ℝ, 0 < v ∧ v ≤ 13/10000 ∧ 11/2 ≤ ((5*n:ℕ):ℝ)*v ∧
      -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hk0 : 0 < k := by linarith
  obtain ⟨τ,hτ,hs⟩ := exists_endpoint_saddle (k/(5*(n:ℝ)^2)) (by positivity) hband
  let v : ℝ := τ/((5*n:ℕ):ℝ)
  have hv : 0 < v := by dsimp [v]; exact div_pos (by linarith) (by positivity)
  have he : ((5*n:ℕ):ℝ)*v=τ := by dsimp [v]; field_simp
  have hs' : -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2) := by rw [he]; exact hs
  exact ⟨v,hv,saddle_radius_small n k v hn hv hk hs',by rw [he]; exact hτ,hs'⟩

/-- In particular the manuscript's n>=31147, k>=5n range meets the same cutoff. -/
theorem exists_global_endpoint_saddle (n : ℕ) (k : ℝ) (hn : 31147 ≤ n) (hk : 5*(n:ℝ) ≤ k)
    (hband : k/(5*(n:ℝ)^2) ≤ -deriv radialR (11/2)) :
    ∃ v : ℝ, 0 < v ∧ v ≤ 13/10000 ∧ 11/2 ≤ ((5*n:ℕ):ℝ)*v ∧
      -deriv radialR (((5*n:ℕ):ℝ)*v)=k/(5*(n:ℝ)^2) := by
  have hnR : (31147:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  exact exists_small_endpoint_saddle n k (by omega) (by linarith) hband

end
end Borwein.EndpointSaddleRange
