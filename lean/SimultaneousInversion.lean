import InversionContinuity
import ProjectiveChartMaps

namespace CurveSymmetry

set_option autoImplicit false
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

abbrev AffineTorus := {v : Fin 2 → ℂ // v 0 ≠ 0 ∧ v 1 ≠ 0}

def torusInvertCoordinate (i : Fin 2) (v : AffineTorus) : AffineTorus :=
  ⟨invertCoordinate i v.val, by
    fin_cases i <;> simp [invertCoordinate, v.property.1, v.property.2]⟩

theorem torusInvertCoordinate_continuous (i : Fin 2) : Continuous (torusInvertCoordinate i) := by
  have hn (v : AffineTorus) : v.val i ≠ 0 := by
    fin_cases i
    · exact v.property.1
    · exact v.property.2
  have hc : Continuous (fun v : AffineTorus => (⟨v.val, hn v⟩ : CoordinateNonzero i)) :=
    continuous_subtype_val.subtype_mk _
  exact ((continuous_invertCoordinate i).comp hc).subtype_mk _

def simultaneousInversion (v : AffineTorus) : AffineTorus :=
  torusInvertCoordinate 1 (torusInvertCoordinate 0 v)

theorem simultaneousInversion_val (v : AffineTorus) :
    (simultaneousInversion v).val = ![(v.val 0)⁻¹, (v.val 1)⁻¹] := by
  ext i
  fin_cases i <;> simp [simultaneousInversion, torusInvertCoordinate, invertCoordinate]

theorem simultaneousInversion_involutive : Function.Involutive simultaneousInversion := by
  intro v
  apply Subtype.ext
  rw [simultaneousInversion_val, simultaneousInversion_val]
  ext i
  fin_cases i <;> simp

def simultaneousInversionHomeomorph : AffineTorus ≃ₜ AffineTorus where
  toFun := simultaneousInversion
  invFun := simultaneousInversion
  left_inv := simultaneousInversion_involutive
  right_inv := simultaneousInversion_involutive
  continuous_toFun := (torusInvertCoordinate_continuous 1).comp (torusInvertCoordinate_continuous 0)
  continuous_invFun := (torusInvertCoordinate_continuous 1).comp (torusInvertCoordinate_continuous 0)

/-- The torus homeomorphism is exactly the finite/reciprocal chart transition. -/
theorem simultaneousInversion_chart (v : AffineTorus) :
    reciprocalProjectiveChart v.val = affineProjectiveChart (simultaneousInversion v).val := by
  rw [simultaneousInversion_val]
  exact reciprocalProjectiveChart_overlap v.val v.property.1 v.property.2

theorem simultaneousInversion_curve (m : ℕ) (α : ℂ) (v : AffineTorus) :
    planeEval (v.val 0) (v.val 1) (familyInfinityPolynomial m α) = 0 ↔
      planeEval ((simultaneousInversion v).val 0) ((simultaneousInversion v).val 1)
        (familyPolynomial m α) = 0 := by
  rw [← reciprocalProjectiveChart_mem, simultaneousInversion_chart,
    affineProjectiveChart_mem]

#print axioms simultaneousInversionHomeomorph
#print axioms simultaneousInversion_curve

end
end CurveSymmetry
