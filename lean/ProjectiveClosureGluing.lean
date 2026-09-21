import AffineChartImages
import OtherMixedCornerClosure
import AffineZariskiTopology
import ProjectiveChartMaps

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

private lemma eval_plane (v : Fin 2 → ℂ) (P : BPoly) :
    eval v P = planeEval (v 0) (v 1) P := by
  unfold planeEval
  have he : (fun i : Fin 2 => if i = 0 then v 0 else v 1) = v := by
    ext i
    fin_cases i <;> rfl
  rw [he]

/-- A property of a subset of the product of projective lines, using the
already checked affine Zariski topology on each chart. This does not declare
a topology on the projective product or assume chart open embeddings. -/
def ClosedInProjectiveCharts (S : Set (ProjectiveLine × ProjectiveLine)) : Prop :=
  IsClosed (affineProjectiveChart ⁻¹' S) ∧
  IsClosed (mixedProjectiveChart ⁻¹' S) ∧
  IsClosed (otherMixedProjectiveChart ⁻¹' S) ∧
  IsClosed (reciprocalProjectiveChart ⁻¹' S)

private theorem chart_closed_extension
    (φ : (Fin 2 → ℂ) → ProjectiveLine × ProjectiveLine)
    (S : Set (ProjectiveLine × ProjectiveLine)) (D : Set (Fin 2 → ℂ)) (Q : BPoly)
    (hs : IsClosed (φ ⁻¹' S)) (hd : φ '' D ⊆ S)
    (hc : closure (affineSpectrumPoint '' D) = PrimeSpectrum.zeroLocus ({Q} : Set BPoly))
    {v : Fin 2 → ℂ} (hv : eval v Q = 0) : φ v ∈ S := by
  have hD : D ⊆ φ ⁻¹' S := by intro w hw; exact hd ⟨w, hw, rfl⟩
  apply closure_minimal hD hs
  rw [affineZariski_embedding.closure_eq_preimage_closure_image, hc]
  change (∀ P ∈ ({Q} : Set BPoly), eval v P = 0)
  simpa using hv

/-- Local density in all charts forces global containment. No genus,
singularity assertion, or unproved projective topology is used. -/
theorem family_projective_chart_gluing {m : ℕ} (hm : 0 < m) (α : ℂ)
    (S : Set (ProjectiveLine × ProjectiveLine)) (hs : ClosedInProjectiveCharts S)
    (hA : affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0} ⊆ S) :
    familyProjectiveCurve m α ⊆ S := by
  intro p hp
  rcases projectiveChart_cover p with ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩ | ⟨v, rfl⟩
  · exact hA ⟨v, (eval_plane v _).trans ((affineProjectiveChart_mem m α v).mp hp), rfl⟩
  · apply chart_closed_extension mixedProjectiveChart S
      {w | eval w (familyMixedPolynomial m α (star α)) = 0 ∧ w 0 ≠ 0}
      (familyMixedPolynomial m α (star α)) hs.2.1
    · rintro _ ⟨w, ⟨hw, h0⟩, rfl⟩
      exact hA ⟨![(w 0)⁻¹, w 1], (mixed_vector_zero_iff m α w h0).mp hw,
        (mixedProjectiveChart_overlap w h0).symm⟩
    · simpa using punctured_complex_points_closure _ _ coordinate_zero_irreducible
        (mixed_not_dvd_coordinate hm α (star α))
    · exact (eval_plane v _).trans ((mixedProjectiveChart_mem m α v).mp hp)
  · apply chart_closed_extension otherMixedProjectiveChart S
      {w | eval w (familyMixedPolynomial m (star α) α) = 0 ∧ w 0 ≠ 0}
      (familyMixedPolynomial m (star α) α) hs.2.2.1
    · rintro _ ⟨w, hw, rfl⟩
      have hi := (Set.ext_iff.mp (other_mixed_affine_points_image m α) w).mpr hw
      obtain ⟨z, ⟨hz, h1⟩, hzw⟩ := hi
      subst w
      apply hA
      refine ⟨z, hz, ?_⟩
      rw [otherMixedProjectiveChart_overlap _ (inv_ne_zero h1)]
      congr 1
      ext i
      fin_cases i <;> simp
    · simpa using punctured_complex_points_closure _ _ coordinate_zero_irreducible
        (mixed_not_dvd_coordinate hm (star α) α)
    · exact (eval_plane v _).trans ((otherMixedProjectiveChart_mem m α v).mp hp)
  · apply chart_closed_extension reciprocalProjectiveChart S
      {w | eval w (familyInfinityPolynomial m α) = 0 ∧ w 0 ≠ 0 ∧ w 1 ≠ 0}
      (familyInfinityPolynomial m α) hs.2.2.2
    · rintro _ ⟨w, ⟨hw, h0, h1⟩, rfl⟩
      exact hA ⟨![(w 0)⁻¹, (w 1)⁻¹], (reciprocal_vector_zero_iff m α w h0 h1).mp hw,
        (reciprocalProjectiveChart_overlap w h0 h1).symm⟩
    · exact reciprocal_chart_complex_closure hm α
    · exact (eval_plane v _).trans ((reciprocalProjectiveChart_mem m α v).mp hp)

/-- The family itself satisfies the same chartwise closedness condition. -/
theorem family_closed_in_projective_charts (m : ℕ) (α : ℂ) :
    ClosedInProjectiveCharts (familyProjectiveCurve m α) := by
  have hA : affineProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyPolynomial m α) = 0} := by
    ext v; exact (affineProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  have hM : mixedProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyMixedPolynomial m α (star α)) = 0} := by
    ext v; exact (mixedProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  have hO : otherMixedProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyMixedPolynomial m (star α) α) = 0} := by
    ext v; exact (otherMixedProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  have hR : reciprocalProjectiveChart ⁻¹' familyProjectiveCurve m α =
      {v | eval v (familyInfinityPolynomial m α) = 0} := by
    ext v; exact (reciprocalProjectiveChart_mem m α v).trans (by simp only [Set.mem_ofPred_eq, eval_plane])
  unfold ClosedInProjectiveCharts
  rw [hA, hM, hO, hR]
  exact ⟨affineZariski_polynomial_zero_closed _, affineZariski_polynomial_zero_closed _,
    affineZariski_polynomial_zero_closed _, affineZariski_polynomial_zero_closed _⟩

section AmbientTopology
variable [TopologicalSpace (ProjectiveLine × ProjectiveLine)]

/-- Conditional ambient closure theorem. Its hypotheses expose the remaining
topology interface: four continuous charts and closedness of the projective
equation. No particular projective topology is silently supplied. -/
theorem family_projective_closure_of_chart_continuity {m : ℕ} (hm : 0 < m) (α : ℂ)
    (hA : Continuous affineProjectiveChart) (hM : Continuous mixedProjectiveChart)
    (hO : Continuous otherMixedProjectiveChart) (hR : Continuous reciprocalProjectiveChart)
    (hV : IsClosed (familyProjectiveCurve m α)) :
    closure (affineProjectiveChart '' {v : Fin 2 → ℂ | eval v (familyPolynomial m α) = 0}) =
      familyProjectiveCurve m α := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ hV
    rintro _ ⟨v, hv, rfl⟩
    exact (affineProjectiveChart_mem m α v).mpr ((eval_plane v _).symm.trans hv)
  · apply family_projective_chart_gluing hm α
    · exact ⟨isClosed_closure.preimage hA, isClosed_closure.preimage hM,
        isClosed_closure.preimage hO, isClosed_closure.preimage hR⟩
    · exact subset_closure

end AmbientTopology

#print axioms family_projective_closure_of_chart_continuity
#print axioms family_projective_chart_gluing
#print axioms family_closed_in_projective_charts

end
end CurveSymmetry
