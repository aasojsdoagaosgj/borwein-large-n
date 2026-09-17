import Borwein.EndpointPhaseBounds

set_option autoImplicit false

namespace Borwein.EndpointScaledBounds
noncomputable section
open EndpointPhaseAtoms EndpointPhaseSeries EndpointPhaseDerivatives EndpointPhaseBounds

def secondProfile (τ : ℝ) (k : ℕ) : ℝ :=
  (8/5)*Real.exp (-τ*(k:ℝ))/(k:ℝ)^2*(1+τ*(k:ℝ)+(τ*(k:ℝ))^2/2)
def thirdProfile (τ : ℝ) (k : ℕ) : ℝ :=
  (24/5)*Real.exp (-τ*(k:ℝ))/(k:ℝ)^2*(1+τ*(k:ℝ)+(τ*(k:ℝ))^2/2+(τ*(k:ℝ))^3/6)

theorem second_identity (n k : ℕ) (v : ℝ) (hv : 0 < v) :
    v^3*(sharpMajorant n 2 0 v k+2*sharpMajorant n 1 1 v k+2*sharpMajorant n 0 2 v k)=
      secondProfile (((5*n:ℕ):ℝ)*v) k := by
  by_cases hk : k=0
  · simp [hk, sharpMajorant, secondProfile]
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hv0 := ne_of_gt hv
  have he : -frequency n k*v = -(((5*n:ℕ):ℝ)*v)*(k:ℝ) := by unfold frequency; ring
  simp only [sharpMajorant, secondProfile, he]
  unfold frequency
  field_simp
  ring

theorem third_identity (n k : ℕ) (v : ℝ) (hv : 0 < v) :
    v^4*(sharpMajorant n 3 0 v k+3*sharpMajorant n 2 1 v k+
      6*sharpMajorant n 1 2 v k+6*sharpMajorant n 0 3 v k)=
      thirdProfile (((5*n:ℕ):ℝ)*v) k := by
  by_cases hk : k=0
  · simp [hk, sharpMajorant, thirdProfile]
  have hk0 : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hv0 := ne_of_gt hv
  have he : -frequency n k*v = -(((5*n:ℕ):ℝ)*v)*(k:ℝ) := by unfold frequency; ring
  simp only [sharpMajorant, thirdProfile, he]
  unfold frequency
  field_simp
  ring

theorem second_hasSum (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasSum (secondProfile (((5*n:ℕ):ℝ)*v))
      (v^3*((∑' k, sharpMajorant n 2 0 v k)+2*(∑' k, sharpMajorant n 1 1 v k)+
        2*(∑' k, sharpMajorant n 0 2 v k))) := by
  have hh := (((sharpMajorant_summable n 2 0 v hn hv).hasSum.add
    ((sharpMajorant_summable n 1 1 v hn hv).hasSum.mul_left 2)).add
    ((sharpMajorant_summable n 0 2 v hn hv).hasSum.mul_left 2)).mul_left (v^3)
  exact hh.congr_fun (fun k => (second_identity n k v hv).symm)

theorem third_hasSum (n : ℕ) (v : ℝ) (hn : 0 < n) (hv : 0 < v) :
    HasSum (thirdProfile (((5*n:ℕ):ℝ)*v))
      (v^4*((∑' k, sharpMajorant n 3 0 v k)+3*(∑' k, sharpMajorant n 2 1 v k)+
        6*(∑' k, sharpMajorant n 1 2 v k)+6*(∑' k, sharpMajorant n 0 3 v k))) := by
  have hh := ((((sharpMajorant_summable n 3 0 v hn hv).hasSum.add
    ((sharpMajorant_summable n 2 1 v hn hv).hasSum.mul_left 3)).add
    ((sharpMajorant_summable n 1 2 v hn hv).hasSum.mul_left 6)).add
    ((sharpMajorant_summable n 0 3 v hn hv).hasSum.mul_left 6)).mul_left (v^4)
  exact hh.congr_fun (fun k => (third_identity n k v hv).symm)

theorem second_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    v^3*‖q2 n v y‖ ≤ ∑' k : ℕ, secondProfile (((5*n:ℕ):ℝ)*v) k := by
  rw [(second_hasSum n v hn hv).tsum_eq]
  exact mul_le_mul_of_nonneg_left (q2_bound n v y hn hv) (by positivity)

theorem third_bound (n : ℕ) (v y : ℝ) (hn : 0 < n) (hv : 0 < v) :
    v^4*‖q3 n v y‖ ≤ ∑' k : ℕ, thirdProfile (((5*n:ℕ):ℝ)*v) k := by
  rw [(third_hasSum n v hn hv).tsum_eq]
  exact mul_le_mul_of_nonneg_left (q3_bound n v y hn hv) (by positivity)

end
end Borwein.EndpointScaledBounds
