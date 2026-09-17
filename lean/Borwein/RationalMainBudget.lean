import Borwein.SignedMainBudget

set_option autoImplicit false

namespace Borwein.RationalMainBudget
noncomputable section
open RadialDerivatives ActualPhaseTaylor AmplitudeTaylor

def aOne (q : ℝ) : ℝ := (77/50)*(16/15)*q
def aTwo (q : ℝ) : ℝ := (77/100)*((64/45)*q+((16/15)*q)^2)
def relative (v w3 w4 z : ℝ) : ℝ :=
  (240*w4/(32*(39/100:ℝ)^2*v^2)+2645*w3^2/(192*(39/100:ℝ)^3*v^3)+z/30)/(22/25)
def absolute (v w3 q z : ℝ) : ℝ :=
  (4*(23*aOne q*w3/(8*(39/100:ℝ)^2*v^2)+aTwo q/(2*(39/100:ℝ)*v))+
    z/30*((8/5:ℝ)*aOne q)+(1232/1875:ℝ)*z*q)/(22/25)

theorem sqrt_lower : (22/25:ℝ) ≤ Real.sqrt (39/50:ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 39/50)
  have hp := Real.sqrt_nonneg (39/50:ℝ)
  nlinarith

theorem radius_upper (τ T : ℝ) (hτ : 0 ≤ τ) (hT : τ ≤ T) :
    EMUniformBounds.radius τ (2/5) ≤ T+2/5 := by
  have hT0 := hτ.trans hT
  have hsq := pow_le_pow_left₀ hτ hT 2
  unfold EMUniformBounds.radius
  apply Real.sqrt_le_iff.mpr
  constructor <;> nlinarith

theorem amplitude_upper (τ q : ℝ) (hq : Real.exp (-τ) ≤ q) :
    a1 τ ≤ aOne q ∧ a2 τ ≤ aTwo q := by
  have he := (Real.exp_pos (-τ)).le
  constructor
  · dsimp [a1,AmplitudeBounds.firstBudget,aOne]
    nlinarith
  · dsimp [a2,AmplitudeBounds.firstBudget,AmplitudeBounds.secondBudget,aTwo]
    gcongr

theorem relative_upper (τ v w3 w4 z : ℝ) (hv : 0 < v) (hV : v ≤ secondDerivative τ)
    (h3 : W 3 τ ≤ w3) (h4 : W 4 τ ≤ w4) (hz : EMUniformBounds.radius τ (2/5) ≤ z) :
    SignedMainBudget.relativeBudget τ ≤ relative v w3 w4 z := by
  have hV0 := secondDerivative_pos τ
  have h30 := W_nonneg 3 τ
  have h40 := W_nonneg 4 τ
  have hw3 := h30.trans h3
  have hw4 := h40.trans h4
  have hz0 : 0 ≤ z := (Real.sqrt_nonneg _).trans hz
  unfold SignedMainBudget.relativeBudget relative
  apply div_le_div₀
  · positivity
  · gcongr
  · norm_num
  · exact sqrt_lower

theorem absolute_upper (τ v w3 q z : ℝ) (hv : 0 < v) (hV : v ≤ secondDerivative τ)
    (h3 : W 3 τ ≤ w3) (hq : Real.exp (-τ) ≤ q) (hz : EMUniformBounds.radius τ (2/5) ≤ z) :
    SignedMainBudget.absoluteBudget τ ≤ absolute v w3 q z := by
  have hV0 := secondDerivative_pos τ
  have h30 := W_nonneg 3 τ
  have hw3 := h30.trans h3
  have he := (Real.exp_pos (-τ)).le
  have hq0 := he.trans hq
  have hr0 : 0 ≤ EMUniformBounds.radius τ (2/5) := Real.sqrt_nonneg _
  have hz0 := hr0.trans hz
  have ha := amplitude_upper τ q hq
  have ha0 := CombinedGaussianError.amplitude_budgets_nonneg τ
  have haQ1 : 0 ≤ aOne q := ha0.1.trans ha.1
  have haQ2 : 0 ≤ aTwo q := ha0.2.trans ha.2
  have ha1 := ha.1
  have ha2 := ha.2
  have ha10 := ha0.1
  have ha20 := ha0.2
  unfold SignedMainBudget.absoluteBudget absolute
  apply div_le_div₀
  · positivity
  · gcongr
  · norm_num
  · exact sqrt_lower

end
end Borwein.RationalMainBudget
