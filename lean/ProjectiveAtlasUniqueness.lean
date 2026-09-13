import ProjectiveAtlasEmbeddings

namespace CurveSymmetry

set_option autoImplicit false
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

/-- The standard affine Zariski charts determine at most one topology on the
projective product in which they are open embeddings. Together with the
constructed embeddings, this characterizes the topology by its affine atlas,
independently of any curve equation. -/
theorem projectiveAtlasTopology_unique
    (t : TopologicalSpace (ProjectiveLine × ProjectiveLine))
    (h : ∀ i, @Topology.IsOpenEmbedding _ _ affineZariskiTopology t (projectiveChart i)) :
    t = projectiveAtlasTopology := by
  letI := t
  apply TopologicalSpace.ext
  funext S
  apply propext
  change IsOpen S ↔ @IsOpen _ projectiveAtlasTopology S
  rw [projectiveAtlas_isOpen_iff]
  constructor
  · intro hs i
    exact hs.preimage (h i).continuous
  · intro hs
    have he : S = ⋃ i, projectiveChart i '' (projectiveChart i ⁻¹' S) := by
      ext p
      constructor
      · intro hp
        obtain ⟨⟨i, v⟩, hv⟩ := projectiveAtlasMap_surjective p
        change projectiveChart i v = p at hv
        exact Set.mem_iUnion.mpr ⟨i, ⟨v, by simpa only [Set.mem_preimage, hv] using hp, hv⟩⟩
      · intro hp
        obtain ⟨i, v, hv, rfl⟩ := Set.mem_iUnion.mp hp
        exact hv
    rw [he]
    exact isOpen_iUnion (fun i => (h i).isOpenMap _ (hs i))

/-- Existence and uniqueness of the topology with these four affine-Zariski
open charts. This is an atlas characterization, not a comparison with a
separately constructed scheme or projective spectrum. -/
theorem projectiveAtlasTopology_characterization
    (t : TopologicalSpace (ProjectiveLine × ProjectiveLine)) :
    (∀ i, @Topology.IsOpenEmbedding _ _ affineZariskiTopology t (projectiveChart i)) ↔
      t = projectiveAtlasTopology := by
  constructor
  · exact projectiveAtlasTopology_unique t
  · rintro rfl
    exact projectiveChart_isOpenEmbedding

#print axioms projectiveAtlasTopology_unique
#print axioms projectiveAtlasTopology_characterization

end
end CurveSymmetry
