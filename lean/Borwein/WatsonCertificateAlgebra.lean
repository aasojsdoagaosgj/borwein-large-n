import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Borwein.WatsonCertificateAlgebra
noncomputable section

def leftStep (q w u v : ℂ) : ℂ := (1-u/v)*(1-u/(w^2*q*v))
def rightStep (q w u v : ℂ) : ℂ := (1-u*v)*(1-w^2*q*u*v)
def rowFactor (q w u : ℂ) : ℂ := (1-u/(w*q))*(1-w*u)
def bracket (q w u v : ℂ) : ℂ := 1-u/(q*v)-w*u*(1-u^2/q)+w^2*q*(1-u*v)

/-- The denominator-cleared telescoping certificate, with no row-factor division. -/
theorem certificate_identity (q w u v : ℂ) (hq : q ≠ 0) (hw : w ≠ 0) (hv : v ≠ 0) :
    (rowFactor q w u*(1-u^2/q)*(1-u^2)-leftStep q w u v*rightStep q w u v)*(1-w^2*q*v^2)=
      w*u*v^2*(1-w*q*v)*bracket q w u v*leftStep q w u v+
      u/(w^2*q*v)*(1-w*v)*bracket q w u (v/q)*rightStep q w u v := by
  unfold rowFactor leftStep rightStep bracket
  field_simp
  <;> ring

end
end Borwein.WatsonCertificateAlgebra
