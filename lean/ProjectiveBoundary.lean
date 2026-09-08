import FamilyProjective

namespace CurveSymmetry

set_option autoImplicit false
open OnePoint

/-- The standard finite-by-finite chart in the product of projective lines. -/
def projectiveAffineChart : Set (ProjectiveLine × ProjectiveLine) :=
  {p | p.1 ≠ sphereProjectiveEquiv (∞ : Sphere) ∧
    p.2 ≠ sphereProjectiveEquiv (∞ : Sphere)}

def familyBoundaryPoints : Set (ProjectiveLine × ProjectiveLine) :=
  {(sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv ((0 : ℂ) : Sphere)),
    (sphereProjectiveEquiv ((0 : ℂ) : Sphere), sphereProjectiveEquiv (∞ : Sphere)),
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere))}

/-- Exactly three points of the constructed curve lie outside the affine
chart. This does not assert that they belong to a Zariski closure. -/
theorem family_projective_boundary {m : ℕ} (hm : 0 < m) (α : ℂ) :
    familyProjectiveCurve m α \ projectiveAffineChart = familyBoundaryPoints := by
  ext ⟨p, q⟩
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  obtain ⟨v, rfl⟩ := sphereProjectiveEquiv.surjective q
  cases u using OnePoint.rec <;> cases v using OnePoint.rec <;>
    simp [projectiveAffineChart, familyBoundaryPoints,
      familyProjective_infinity_finite hm, familyProjective_finite_infinity hm,
      familyProjective_infinity_infinity hm]

/-- The full set is its affine part together with the explicit boundary.
The missing closure step is therefore confined to the boundary, once the
affine/projective Zariski-chart interface has been supplied. -/
theorem family_projective_affine_union_boundary {m : ℕ} (hm : 0 < m) (α : ℂ) :
    familyProjectiveCurve m α =
      (familyProjectiveCurve m α ∩ projectiveAffineChart) ∪ familyBoundaryPoints := by
  rw [← family_projective_boundary hm α]
  exact (Set.inter_union_sdiff _ _).symm

#print axioms family_projective_boundary
#print axioms family_projective_affine_union_boundary

end CurveSymmetry
