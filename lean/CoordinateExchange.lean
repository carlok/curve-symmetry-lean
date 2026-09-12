import PolynomialZariskiMaps
import ProjectiveChartMaps

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

def exchangeCoordinates (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![v 1, v 0]

theorem exchangeCoordinates_involutive : Function.Involutive exchangeCoordinates := by
  intro v
  ext i
  fin_cases i <;> rfl

noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

theorem exchangeCoordinates_continuous : Continuous exchangeCoordinates := by
  have he : polynomialPointMap ![X 1, X 0] = exchangeCoordinates := by
    funext v i
    fin_cases i <;> simp [polynomialPointMap, exchangeCoordinates]
  rw [← he]
  exact polynomialPointMap_continuous _

/-- Coordinate exchange is a homeomorphism for the complex-point Zariski
topology, not just the usual Euclidean topology. -/
def coordinateExchangeHomeomorph : (Fin 2 → ℂ) ≃ₜ (Fin 2 → ℂ) where
  toFun := exchangeCoordinates
  invFun := exchangeCoordinates
  left_inv := exchangeCoordinates_involutive
  right_inv := exchangeCoordinates_involutive
  continuous_toFun := exchangeCoordinates_continuous
  continuous_invFun := exchangeCoordinates_continuous

/-- The overlap where both coordinates are nonzero is preserved. -/
theorem exchangeCoordinates_nonzero (v : Fin 2 → ℂ) :
    ((exchangeCoordinates v) 0 ≠ 0 ∧ (exchangeCoordinates v) 1 ≠ 0) ↔
      (v 0 ≠ 0 ∧ v 1 ≠ 0) := by
  simp [exchangeCoordinates, and_comm]

def coordinateExchangeTorusHomeomorph :
    {v : Fin 2 → ℂ // v 0 ≠ 0 ∧ v 1 ≠ 0} ≃ₜ
      {v : Fin 2 → ℂ // v 0 ≠ 0 ∧ v 1 ≠ 0} where
  toFun v := ⟨exchangeCoordinates v.val, (exchangeCoordinates_nonzero v.val).mpr v.property⟩
  invFun v := ⟨exchangeCoordinates v.val, (exchangeCoordinates_nonzero v.val).mpr v.property⟩
  left_inv v := Subtype.ext (exchangeCoordinates_involutive v.val)
  right_inv v := Subtype.ext (exchangeCoordinates_involutive v.val)
  continuous_toFun := (exchangeCoordinates_continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (exchangeCoordinates_continuous.comp continuous_subtype_val).subtype_mk _

theorem affineProjectiveChart_exchange (v : Fin 2 → ℂ) :
    affineProjectiveChart (exchangeCoordinates v) = (affineProjectiveChart v).swap := rfl

theorem reciprocalProjectiveChart_exchange (v : Fin 2 → ℂ) :
    reciprocalProjectiveChart (exchangeCoordinates v) = (reciprocalProjectiveChart v).swap := rfl

/-- The reversed coordinate order of the second mixed chart already accounts
for exchanging the projective factors; no extra coordinate swap belongs here. -/
theorem mixedProjectiveChart_factor_exchange (v : Fin 2 → ℂ) :
    otherMixedProjectiveChart v = (mixedProjectiveChart v).swap := rfl

#print axioms coordinateExchangeHomeomorph
#print axioms coordinateExchangeTorusHomeomorph

end
end CurveSymmetry
