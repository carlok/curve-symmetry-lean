import ProjectiveClosureGluing
import Mathlib.Topology.Constructions

namespace CurveSymmetry

set_option autoImplicit false
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

def projectiveChart (i : Fin 4) : (Fin 2 → ℂ) → ProjectiveLine × ProjectiveLine :=
  ![affineProjectiveChart, mixedProjectiveChart, otherMixedProjectiveChart,
    reciprocalProjectiveChart] i

abbrev ProjectiveAtlasDomain := Σ _ : Fin 4, (Fin 2 → ℂ)

def projectiveAtlasMap (p : ProjectiveAtlasDomain) : ProjectiveLine × ProjectiveLine :=
  projectiveChart p.1 p.2

theorem projectiveAtlasMap_surjective : Function.Surjective projectiveAtlasMap := by
  intro p
  rcases projectiveChart_cover p with ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩ | ⟨v, hv⟩
  · exact ⟨⟨0, v⟩, hv⟩
  · exact ⟨⟨1, v⟩, hv⟩
  · exact ⟨⟨2, v⟩, hv⟩
  · exact ⟨⟨3, v⟩, hv⟩

/-- Final topology from the disjoint union of the four affine Zariski charts.
The definition is independent of every family equation and parameter. Agreement
with standard projective Zariski geometry still requires chart compatibility;
this name intentionally does not assert that identification. -/
abbrev projectiveAtlasTopology : TopologicalSpace (ProjectiveLine × ProjectiveLine) :=
  TopologicalSpace.coinduced projectiveAtlasMap inferInstance

local instance : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

theorem projectiveAtlasMap_continuous : Continuous projectiveAtlasMap :=
  continuous_coinduced_rng

theorem projectiveChart_continuous (i : Fin 4) : Continuous (projectiveChart i) :=
  projectiveAtlasMap_continuous.comp continuous_sigmaMk

/-- Closedness in this family-independent final topology is exactly the
previously defined chartwise closedness predicate. -/
theorem projectiveAtlas_isClosed_iff (S : Set (ProjectiveLine × ProjectiveLine)) :
    IsClosed S ↔ ClosedInProjectiveCharts S := by
  rw [isClosed_coinduced, isClosed_sigma_iff]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i <;> assumption

#print axioms projectiveAtlasMap_surjective
#print axioms projectiveChart_continuous
#print axioms projectiveAtlas_isClosed_iff

end
end CurveSymmetry
