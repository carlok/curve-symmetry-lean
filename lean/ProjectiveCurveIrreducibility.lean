import ProjectiveAtlasUniqueness
import ProjectiveAtlasClosure

namespace CurveSymmetry

set_option autoImplicit false
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology
local instance : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

private theorem affine_irreducible_of_spectrum_image (S : Set (Fin 2 → ℂ))
    (h : IsIrreducible (affineSpectrumPoint '' S)) : IsIrreducible S := by
  refine ⟨?_, ?_⟩
  · obtain ⟨_, v, hv, rfl⟩ := h.nonempty
    exact ⟨v, hv⟩
  · intro U V hU hV hSU hSV
    obtain ⟨A, hA, rfl⟩ := affineZariski_embedding.isInducing.isOpen_iff.mp hU
    obtain ⟨B, hB, rfl⟩ := affineZariski_embedding.isInducing.isOpen_iff.mp hV
    obtain ⟨u, hu, hAu⟩ := hSU
    obtain ⟨v, hv, hBv⟩ := hSV
    obtain ⟨_, ⟨w, hw, rfl⟩, hAw, hBw⟩ := h.2 A B hA hB
      ⟨affineSpectrumPoint u, ⟨u, hu, rfl⟩, hAu⟩
      ⟨affineSpectrumPoint v, ⟨v, hv, rfl⟩, hBv⟩
    exact ⟨w, hw, hAw, hBw⟩

/-- The actual real diagonal is irreducible in the complex affine Zariski
topology, not in its Euclidean topology. -/
theorem affineRealDiagonal_isIrreducible {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) : IsIrreducible (affineRealDiagonal P) := by
  apply affine_irreducible_of_spectrum_image
  apply PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.mpr
  rw [spectrum_vanishingIdeal_image, real_diagonal_vanishingIdeal hP hinf]
  exact Ideal.isPrime_span_singleton_of_prime hP.prime

/-- Topological irreducibility of the whole complex projective curve, including
its boundary, in the uniquely characterized affine-atlas topology. -/
theorem familyProjectiveCurve_isIrreducible {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) : IsIrreducible (familyProjectiveCurve m α) := by
  rw [← family_projectiveAtlas_real_closure hm ha]
  exact ((affineRealDiagonal_isIrreducible (familyPolynomial_irreducible hm ha)
    (family_realLocus_infinite hm ha)).image affineProjectiveChart
      (projectiveChart_continuous 0).continuousOn).closure

#print axioms affineRealDiagonal_isIrreducible
#print axioms familyProjectiveCurve_isIrreducible

end
end CurveSymmetry
