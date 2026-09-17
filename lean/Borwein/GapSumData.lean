import Borwein.CheckedWeights

namespace Borwein.GapSumData
open scoped BigOperators

def A (d : Fin 4) (i : ℕ) : ℕ := min 4000 (6*(d.val+1)*(i+1))
def term (d : Fin 4) (i : ℕ) : ℤ :=
  ((Borwein.RoundedWeightData.lo d i:ℤ)-(Borwein.RoundedWeightData.hi d (i+1):ℤ))*
    (i+1:ℕ)*(A d i:ℤ)^2*(80000000-(A d i:ℤ)^2)
def block (k : ℕ) : ℤ := ∑ d : Fin 4, ∑ j ∈ Finset.range 25, term d (25*k+j)
def total : ℤ := ∑ d : Fin 4, ∑ i ∈ Finset.range 400, term d i
def denominator : ℕ := 768000000000000000000000000000

end Borwein.GapSumData

