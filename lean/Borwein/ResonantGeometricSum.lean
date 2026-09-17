import Borwein.ResonantArgumentBounds
import Borwein.FiniteBlockLocalization

set_option autoImplicit false

namespace Borwein.ResonantGeometricSum
noncomputable section
open Complex DirichletCover ResonantArgumentBounds FiniteBlockLocalization

def geometricSum (M : ℕ) (z : ℂ) : ℂ := ∑ j ∈ Finset.range M, z^(j+1)

theorem geometric_add (M N : ℕ) (z : ℂ) :
    geometricSum (M+N) z = geometricSum M z+z^M*geometricSum N z := by
  unfold geometricSum
  rw [Finset.sum_range_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_add]
  congr 1

theorem fourier_block_difference (n : ℕ) (z : ℂ) :
    FiniteFourierKernel.finiteSum n z = geometricSum (5*n) z-geometricSum n (z^5) := by
  induction n with
  | zero => simp [FiniteFourierKernel.finiteSum,geometricSum]
  | succ n ih =>
    rw [FiniteFourierKernel.finiteSum_blocks] at ih ⊢
    rw [Finset.sum_range_succ]
    rw [show 5*(n+1) = 5*n+5 by omega,geometric_add,geometric_add n 1]
    have h1 (w : ℂ) : geometricSum 1 w = w := by simp [geometricSum]
    have h5 : geometricSum 5 z = z+z^2+z^3+z^4+z^5 := by
      norm_num [geometricSum,Finset.sum_range_succ]
    rw [h1,h5]
    simp only [pow_mul] at ih ⊢
    linear_combination ih

theorem resonant_phase (q : ℚ) (l : ℕ) (hl : q.den ∣ l) :
    Complex.exp ((l:ℂ)*(2*(Real.pi:ℂ)*I)*(q:ℂ)) = 1 := by
  obtain ⟨u,hu⟩ := hl
  apply Complex.exp_eq_one_iff.mpr
  refine ⟨(u:ℤ)*q.num,?_⟩
  rw [hu,Rat.cast_def]
  push_cast
  have hb : (q.den:ℂ) ≠ 0 := by exact_mod_cast q.den_nz
  field_simp

theorem point_power_exp (n l : ℕ) (τ θ : ℝ) :
    (point n τ θ)^l = Complex.exp (-(l:ℂ)*(τ:ℂ)/(5*(n:ℂ))+(l:ℂ)*(θ:ℂ)*I) := by
  rw [point_pow,AngularKernel.circle_eq_exp,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem resonant_power (n M d k j : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 0 < n) (hM : 0 < M) (hMd : M*d = 5*n) (hk : q.den ∣ d*k) :
    (point n τ θ)^((d*k)*(j+1)) =
      Complex.exp (-argument n τ θ q k*(((j+1:ℕ):ℂ)/(M:ℂ))) := by
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm0 : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hmd : (M:ℂ)*(d:ℂ) = 5*(n:ℂ) := by exact_mod_cast hMd
  have hr := resonant_phase q ((d*k)*(j+1)) (dvd_mul_of_dvd_left hk _)
  rw [point_power_exp]
  have he : -(((d*k)*(j+1):ℕ):ℂ)*(τ:ℂ)/(5*(n:ℂ))+
      (((d*k)*(j+1):ℕ):ℂ)*(θ:ℂ)*I =
      -argument n τ θ q k*(((j+1:ℕ):ℂ)/(M:ℂ))+
        (((d*k)*(j+1):ℕ):ℂ)*(2*(Real.pi:ℂ)*I)*(q:ℂ) := by
    unfold argument localAngle
    push_cast
    field_simp
    linear_combination (k:ℂ)*(-(τ:ℂ)+(5*(n:ℂ))*(θ:ℂ)*I-
      10*(n:ℂ)*(Real.pi:ℂ)*(q:ℂ)*I)*hmd
  rw [he,Complex.exp_add,hr,mul_one]

theorem resonant_sum (n M d k : ℕ) (τ θ : ℝ) (q : ℚ)
    (hn : 0 < n) (hM : 0 < M) (hMd : M*d = 5*n) (hk : q.den ∣ d*k) :
    geometricSum M ((point n τ θ)^(d*k)) =
      ResonantQuadrature.finiteSum M (argument n τ θ q k) := by
  unfold geometricSum ResonantQuadrature.finiteSum
  apply Finset.sum_congr rfl
  intro j _
  rw [← pow_mul]
  exact resonant_power n M d k j τ θ q hn hM hMd hk

end
end Borwein.ResonantGeometricSum
