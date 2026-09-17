import Borwein.EulerGaussianLimit
import Borwein.IntegerQBinomial

set_option autoImplicit false

namespace Borwein.RogersGaussianLimit
noncomputable section
open Complex EndpointEta EndpointEulerTail EulerQBinomial EulerGaussianLimit Filter
open scoped Topology

theorem fixed_column (q : ℂ) (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun n : ℕ => gaussian q n k) atTop (𝓝 ((finiteEuler k q)⁻¹)) := by
  have hp := finiteEuler_tendsto q hq
  have hh := hp.div (tendsto_const_nhds.mul (hp.comp (tendsto_sub_atTop_nat k)))
    (mul_ne_zero (finiteEuler_ne_zero k q hq) (euler_ne_zero q hq))
  have he : euler q/(finiteEuler k q*euler q)=(finiteEuler k q)⁻¹ := by
    field_simp [euler_ne_zero q hq, finiteEuler_ne_zero k q hq]
  rw [he] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop k] with n hn
  simp only [Function.comp_def, Pi.div_apply, gaussian, if_pos hn] 

theorem integer_bound (q : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ n k : ℕ, ‖gaussian q n k‖ ≤ M) (n : ℕ) (k : ℤ) :
    ‖IntegerQBinomial.choose q n k‖ ≤ M := by
  unfold IntegerQBinomial.choose
  split_ifs
  · exact hb _ _
  · simpa using hM

theorem shifted_central (q : ℂ) (hq : ‖q‖ < 1) (a : ℕ) (j : ℤ) :
    Tendsto (fun n : ℕ => IntegerQBinomial.choose q (2*n+a) ((n:ℤ)-2*j))
      atTop (𝓝 ((euler q)⁻¹)) := by
  have habs : -(j.natAbs:ℤ) ≤ j ∧ j ≤ (j.natAbs:ℤ) := by
    rw [Int.natCast_natAbs]
    exact abs_le.mp (le_refl |j|)
  have hg : Tendsto (fun n : ℕ => ((n:ℤ)-2*j).toNat) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_sub_atTop_nat (2*j.natAbs))
    intro n
    omega
  have hd : Tendsto (fun n : ℕ => 2*n+a-((n:ℤ)-2*j).toNat) atTop atTop := by
    apply tendsto_atTop_mono _ (tendsto_sub_atTop_nat (2*j.natAbs))
    intro n
    omega
  have hle : ∀ᶠ n : ℕ in atTop, ((n:ℤ)-2*j).toNat ≤ 2*n+a := by
    filter_upwards [eventually_ge_atTop (2*j.natAbs)] with n hn
    omega
  have hh := gaussian_tendsto q (fun n => 2*n+a) (fun n => ((n:ℤ)-2*j).toNat) hq
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 2*n+a by omega) tendsto_id) hg hd hle
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2*j.natAbs)] with n hn
  rw [IntegerQBinomial.choose, if_pos (by omega)]

end
end Borwein.RogersGaussianLimit
