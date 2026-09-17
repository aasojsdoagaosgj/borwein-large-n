import Borwein.FiveRootProductExpansion

namespace Borwein.FifthRootCoordinates
noncomputable section
open Complex

theorem coordinate_square (ξ : ℂ) (hξ : ξ^5 = 1) : ξ.re^2+ξ.im^2 = 1 := by
  have h := FiveRootProductExpansion.root_norm ξ hξ
  have hs := Complex.sq_norm ξ
  rw [h] at hs
  simpa [Complex.normSq_apply,pow_two] using hs.symm

theorem real_quadratic (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) :
    4*ξ.re^2+2*ξ.re-1 = 0 := by
  have hn := FiveRootProductExpansion.root_norm ξ hξ
  have hz : ξ ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; norm_num)
  have hu : starRingEnd ℂ ξ*ξ = 1 := by
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,hn]
    norm_num
  have h4 : ξ^4 = starRingEnd ℂ ξ := by
    apply mul_right_cancel₀ hz
    rw [← pow_succ,hu]
    exact hξ
  have h3 : ξ^3 = (starRingEnd ℂ ξ)^2 := by
    rw [← h4,← pow_mul,show 4*2 = 5+3 by decide,pow_add,hξ,one_mul]
  have hp : ξ^4+ξ^3+ξ^2+ξ+1 = 0 := by
    have he : (ξ^4+ξ^3+ξ^2+ξ+1)*(ξ-1) = ξ^5-1 := by ring
    rw [hξ,sub_self] at he
    exact (mul_eq_zero.mp he).resolve_right (sub_ne_zero.mpr hne)
  rw [h4,h3] at hp
  have hr := congrArg Complex.re hp
  simp [pow_two,Complex.mul_re] at hr
  have hs := coordinate_square ξ hξ
  nlinarith

theorem real_upper (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) : ξ.re ≤ 3091/10000 := by
  have h := real_quadratic ξ hξ hne
  by_contra hh
  have ht := lt_of_not_ge hh
  nlinarith [sq_nonneg (ξ.re-3091/10000)]

theorem imaginary_upper (ξ : ℂ) (hξ : ξ^5 = 1) (hne : ξ ≠ 1) : |ξ.im| ≤ 9511/10000 := by
  have hr := real_upper ξ hξ hne
  have hq := real_quadratic ξ hξ hne
  have hs := coordinate_square ξ hξ
  have ha := sq_abs ξ.im
  nlinarith [abs_nonneg ξ.im]

end
end Borwein.FifthRootCoordinates
