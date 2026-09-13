import ProjectiveAtlasOpenCover
import SimultaneousInversion
import CoordinateExchange

namespace CurveSymmetry

set_option autoImplicit false
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology
local instance : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

private theorem overlap_preimage_open
    (g : (Fin 2 → ℂ) → ProjectiveLine × ProjectiveLine)
    (D : Set (Fin 2 → ℂ)) (hD : IsOpen D)
    (hd : g ⁻¹' Set.range affineProjectiveChart = D)
    (t : D → (Fin 2 → ℂ)) (ht : Continuous t)
    (he : ∀ v : D, g v.val = affineProjectiveChart (t v))
    (U : Set (Fin 2 → ℂ)) (hU : IsOpen U) :
    IsOpen (g ⁻¹' (affineProjectiveChart '' U)) := by
  have hs : g ⁻¹' (affineProjectiveChart '' U) = Subtype.val '' (t ⁻¹' U) := by
    ext v
    constructor
    · rintro ⟨w, hw, hfw⟩
      have hv : v ∈ D := by
        rw [← hd]
        exact ⟨w, hfw⟩
      refine ⟨⟨v, hv⟩, ?_, rfl⟩
      have htval : t ⟨v, hv⟩ = w :=
        affineProjectiveChart_injective ((he ⟨v, hv⟩).symm.trans hfw.symm)
      simpa only [Set.mem_preimage, htval] using hw
    · rintro ⟨v, hv, rfl⟩
      exact ⟨t v, hv, (he v).symm⟩
  rw [hs]
  exact hD.isOpenMap_subtype_val _ (hU.preimage ht)

/-- The affine chart sends every affine-Zariski open set to an open subset of
the chart-final projective space. The proof checks all other chart preimages
using inversion transitions on their actual nonzero domains. -/
theorem affineProjectiveChart_isOpenMap : IsOpenMap affineProjectiveChart := by
  intro U hU
  apply (projectiveAtlas_isOpen_iff _).mpr
  intro i
  fin_cases i
  · change IsOpen (affineProjectiveChart ⁻¹' (affineProjectiveChart '' U))
    simpa only [Set.preimage_image_eq _ affineProjectiveChart_injective] using hU
  · apply overlap_preimage_open mixedProjectiveChart {v | v 0 ≠ 0}
      (affineZariski_coordinate_nonzero_open 0)
      (projectiveChart_affine_overlap_domains 1)
      (fun v => invertCoordinate 0 v.val) (continuous_invertCoordinate 0) _ U hU
    intro v
    rw [mixedProjectiveChart_overlap v.val v.property]
    congr 1
    ext j
    fin_cases j <;> simp [invertCoordinate]
  · apply overlap_preimage_open otherMixedProjectiveChart {v | v 0 ≠ 0}
      (affineZariski_coordinate_nonzero_open 0)
      (projectiveChart_affine_overlap_domains 2)
      (fun v => exchangeCoordinates (invertCoordinate 0 v.val))
      (exchangeCoordinates_continuous.comp (continuous_invertCoordinate 0)) _ U hU
    intro v
    rw [otherMixedProjectiveChart_overlap v.val v.property]
    congr 1
  · exact overlap_preimage_open reciprocalProjectiveChart
      {v | v 0 ≠ 0 ∧ v 1 ≠ 0} affineZariski_both_coordinates_nonzero_open
      (projectiveChart_affine_overlap_domains 3)
      (fun v => (simultaneousInversion v).val)
      (continuous_subtype_val.comp simultaneousInversionHomeomorph.continuous)
      simultaneousInversion_chart U hU

/-- The affine chart has precisely the affine Zariski topology as its subspace
topology, and its image is open. No embedding assumption is used. -/
theorem affineProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding affineProjectiveChart :=
  .of_continuous_injective_isOpenMap (projectiveChart_continuous 0)
    affineProjectiveChart_injective affineProjectiveChart_isOpenMap

#print axioms affineProjectiveChart_isOpenMap
#print axioms affineProjectiveChart_isOpenEmbedding

end
end CurveSymmetry
