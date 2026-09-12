import ProjectiveAtlasTopology

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology
local instance : TopologicalSpace (ProjectiveLine × ProjectiveLine) :=
  projectiveAtlasTopology

theorem family_projectiveAtlas_isClosed (m : ℕ) (α : ℂ) :
    IsClosed (familyProjectiveCurve m α) :=
  (projectiveAtlas_isClosed_iff _).mpr (family_closed_in_projective_charts m α)

/-- Closure in the family-independent chart-final topology. Identification of
that topology with standard projective Zariski geometry is a separate task. -/
theorem family_projectiveAtlas_affine_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure (affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0}) =
      familyProjectiveCurve m α :=
  family_projective_closure_of_chart_continuity hm α
    (projectiveChart_continuous 0) (projectiveChart_continuous 1)
    (projectiveChart_continuous 2) (projectiveChart_continuous 3)
    (family_projectiveAtlas_isClosed m α)

/-- The real diagonal already has the entire complex curve as its closure in
the chart-final topology, including the three boundary points. -/
theorem family_projectiveAtlas_real_closure {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) :
    closure (affineProjectiveChart '' affineRealDiagonal (familyPolynomial m α)) =
      familyProjectiveCurve m α := by
  have hc := affineZariski_real_diagonal_closure
    (familyPolynomial_irreducible hm ha) (family_realLocus_infinite hm ha)
  apply Set.Subset.antisymm
  · calc
      closure (affineProjectiveChart '' affineRealDiagonal (familyPolynomial m α)) ⊆
          closure (affineProjectiveChart ''
            {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0}) := by
        apply closure_mono (Set.image_mono _)
        rw [← hc]
        exact subset_closure
      _ = familyProjectiveCurve m α := family_projectiveAtlas_affine_closure hm α
  · apply family_projective_chart_gluing hm α
    · exact (projectiveAtlas_isClosed_iff _).mp isClosed_closure
    · have hd : affineRealDiagonal (familyPolynomial m α) ⊆
          affineProjectiveChart ⁻¹'
            closure (affineProjectiveChart '' affineRealDiagonal (familyPolynomial m α)) := by
        intro v hv
        exact subset_closure ⟨v, hv, rfl⟩
      have he := closure_minimal hd
        (isClosed_closure.preimage (projectiveChart_continuous 0))
      rw [hc] at he
      rintro _ ⟨v, hv, rfl⟩
      exact he hv

#print axioms family_projectiveAtlas_isClosed
#print axioms family_projectiveAtlas_affine_closure
#print axioms family_projectiveAtlas_real_closure

end
end CurveSymmetry
