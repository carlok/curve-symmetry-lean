import ProjectiveAtlasTopology

namespace CurveSymmetry

set_option autoImplicit false
open OnePoint
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology
local instance : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

theorem projectiveAtlas_isOpen_iff (S : Set (ProjectiveLine × ProjectiveLine)) :
    IsOpen S ↔ ∀ i, IsOpen (projectiveChart i ⁻¹' S) := by
  rw [isOpen_coinduced, isOpen_sigma_iff]
  rfl

private lemma affine_ne_infinity (z : ℂ) :
    affineLinePoint z ≠ sphereProjectiveEquiv (∞ : Sphere) :=
  (affineLinePoint_range _).mp ⟨z, rfl⟩

private lemma reciprocal_ne_zero (z : ℂ) :
    reciprocalLinePoint z ≠ affineLinePoint 0 :=
  (reciprocalLinePoint_range _).mp ⟨z, rfl⟩

private lemma reciprocal_ne_infinity (z : ℂ) :
    reciprocalLinePoint z ≠ sphereProjectiveEquiv (∞ : Sphere) ↔ z ≠ 0 := by
  change reciprocalLinePoint z ≠ reciprocalLinePoint 0 ↔ z ≠ 0
  exact reciprocalLinePoint_injective.ne_iff

/-- Exact affine-chart overlap domains, including the reversed coordinate order
in the second mixed chart. -/
theorem projectiveChart_affine_overlap_domains (i : Fin 4) :
    projectiveChart i ⁻¹' Set.range affineProjectiveChart =
      ![Set.univ, {v | v 0 ≠ 0}, {v | v 0 ≠ 0},
        {v : Fin 2 → ℂ | v 0 ≠ 0 ∧ v 1 ≠ 0}] i := by
  ext v
  fin_cases i <;>
    simp only [Set.mem_preimage, projectiveChart, Matrix.cons_val_zero',
      Matrix.cons_val_succ', affineProjectiveChart_range] <;>
    simp [affineProjectiveChart,
      mixedProjectiveChart, otherMixedProjectiveChart, reciprocalProjectiveChart,
      affine_ne_infinity, reciprocal_ne_infinity]

/-- Every chart range is open; no embedding property is assumed here. -/
theorem projectiveChart_range_isOpen (j : Fin 4) : IsOpen (Set.range (projectiveChart j)) := by
  apply (projectiveAtlas_isOpen_iff _).mpr
  intro i
  have h0 := affineZariski_coordinate_nonzero_open 0
  have h1 := affineZariski_coordinate_nonzero_open 1
  have h01 := h0.inter h1
  have h10 := h1.inter h0
  have he (i j : Fin 4) : projectiveChart i ⁻¹' Set.range (projectiveChart j) =
      ![![Set.univ, {v | v 0 ≠ 0}, {v | v 0 ≠ 0}, {v | v 0 ≠ 0 ∧ v 1 ≠ 0}],
        ![{v | v 0 ≠ 0}, Set.univ, {v | v 1 ≠ 0 ∧ v 0 ≠ 0}, {v | v 1 ≠ 0}],
        ![{v | v 1 ≠ 0}, {v | v 0 ≠ 0 ∧ v 1 ≠ 0}, Set.univ, {v | v 0 ≠ 0}],
        ![{v | v 0 ≠ 0 ∧ v 1 ≠ 0}, {v | v 1 ≠ 0}, {v | v 1 ≠ 0}, Set.univ]] j i := by
    ext v
    fin_cases j <;> fin_cases i <;>
      simp only [Set.mem_preimage, projectiveChart, Matrix.cons_val_zero',
        Matrix.cons_val_succ', affineProjectiveChart_range, mixedProjectiveChart_range,
        otherMixedProjectiveChart_range, reciprocalProjectiveChart_range] <;>
      simp [affineProjectiveChart, mixedProjectiveChart, otherMixedProjectiveChart,
        reciprocalProjectiveChart, affine_ne_infinity, reciprocal_ne_zero,
        reciprocal_ne_infinity, affineLinePoint_injective.ne_iff]
  rw [he]
  fin_cases j <;> fin_cases i <;>
    first | exact isOpen_univ | exact h0 | exact h1 | exact h01 | exact h10

theorem projectiveChart_open_cover :
    (⋃ i, Set.range (projectiveChart i)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨⟨i, v⟩, hp⟩ := projectiveAtlasMap_surjective p
  exact Set.mem_iUnion.mpr ⟨i, ⟨v, hp⟩⟩

#print axioms projectiveChart_affine_overlap_domains
#print axioms projectiveChart_range_isOpen
#print axioms projectiveChart_open_cover

end
end CurveSymmetry
