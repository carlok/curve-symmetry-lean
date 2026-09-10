import FamilyProjective

namespace CurveSymmetry

noncomputable section
open OnePoint

set_option autoImplicit false

/-- Standard projective-line charts `[z:1]` and `[1:z]`. These definitions
make no topological assertion. -/
def affineLinePoint (z : ℂ) : ProjectiveLine :=
  Projectivization.mk ℂ ![z, 1] (by simp)

def reciprocalLinePoint (z : ℂ) : ProjectiveLine :=
  Projectivization.mk ℂ ![1, z] (by simp)

theorem reciprocalLinePoint_overlap {z : ℂ} (hz : z ≠ 0) :
    reciprocalLinePoint z = affineLinePoint z⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z, ?_⟩
  ext i
  fin_cases i <;> simp [hz]

def affineProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (affineLinePoint (w 0), affineLinePoint (w 1))

def mixedProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (reciprocalLinePoint (w 0), affineLinePoint (w 1))

/-- The second mixed chart uses the order `(1/Y,X)`, as in the closure proof. -/
def otherMixedProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (affineLinePoint (w 1), reciprocalLinePoint (w 0))

def reciprocalProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (reciprocalLinePoint (w 0), reciprocalLinePoint (w 1))

theorem mixedProjectiveChart_overlap (w : Fin 2 → ℂ) (h0 : w 0 ≠ 0) :
    mixedProjectiveChart w = affineProjectiveChart ![(w 0)⁻¹, w 1] := by
  simp [mixedProjectiveChart, affineProjectiveChart, reciprocalLinePoint_overlap h0]

theorem otherMixedProjectiveChart_overlap (w : Fin 2 → ℂ) (h0 : w 0 ≠ 0) :
    otherMixedProjectiveChart w = affineProjectiveChart ![w 1, (w 0)⁻¹] := by
  simp [otherMixedProjectiveChart, affineProjectiveChart, reciprocalLinePoint_overlap h0]

theorem reciprocalProjectiveChart_overlap (w : Fin 2 → ℂ)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    reciprocalProjectiveChart w = affineProjectiveChart ![(w 0)⁻¹, (w 1)⁻¹] := by
  simp [reciprocalProjectiveChart, affineProjectiveChart,
    reciprocalLinePoint_overlap h0, reciprocalLinePoint_overlap h1]

theorem affineProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    affineProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyPolynomial m α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_affine])

theorem mixedProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    mixedProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyMixedPolynomial m α (star α)) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_mixed])

theorem otherMixedProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    otherMixedProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyMixedPolynomial m (star α) α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_other_mixed])

theorem reciprocalProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    reciprocalProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyInfinityPolynomial m α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_reciprocal])

/-- The chart origins are precisely the three previously classified boundary
points. This is an identity of points, not a closure or gluing theorem. -/
theorem projectiveChart_origins :
    mixedProjectiveChart ![0, 0] =
      (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv ((0 : ℂ) : Sphere)) ∧
    otherMixedProjectiveChart ![0, 0] =
      (sphereProjectiveEquiv ((0 : ℂ) : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∧
    reciprocalProjectiveChart ![0, 0] =
      (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere)) := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms reciprocalProjectiveChart_overlap
#print axioms projectiveChart_origins

end
end CurveSymmetry
