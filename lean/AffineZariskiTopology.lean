import AffineClosure

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- Zariski topology on complex coordinate points, induced by their evaluation
ideals in Mathlib's prime spectrum. This does not replace the Euclidean
topology on `ℂ` or install a global instance on coordinate vectors. -/
noncomputable abbrev affineZariskiTopology : TopologicalSpace (Fin 2 → ℂ) :=
  TopologicalSpace.induced affineSpectrumPoint inferInstance

theorem affineSpectrumPoint_injective : Function.Injective affineSpectrumPoint := by
  intro v w h
  ext i
  have hp : X i - C (v i) ∈ (affineSpectrumPoint v).asIdeal := by
    change eval v (X i - C (v i)) = 0
    simp
  rw [h] at hp
  change eval w (X i - C (v i)) = 0 at hp
  have he : w i - v i = 0 := by simpa using hp
  exact (sub_eq_zero.mp he).symm

noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

/-- Evaluation identifies complex points with a topological subspace of the
prime spectrum for the explicitly induced Zariski topology. -/
theorem affineZariski_embedding : Topology.IsEmbedding affineSpectrumPoint :=
  ⟨⟨rfl⟩, affineSpectrumPoint_injective⟩

theorem affineZariski_polynomial_nonzero_open (P : BPoly) :
    IsOpen {v : Fin 2 → ℂ | eval v P ≠ 0} := by
  exact (PrimeSpectrum.basicOpen P).isOpen.preimage affineZariski_embedding.continuous

theorem affineZariski_polynomial_zero_closed (P : BPoly) :
    IsClosed {v : Fin 2 → ℂ | eval v P = 0} := by
  simpa only [Set.compl_ofPred, not_not] using
    (affineZariski_polynomial_nonzero_open P).isClosed_compl

theorem affineZariski_coordinate_nonzero_open (i : Fin 2) :
    IsOpen {v : Fin 2 → ℂ | v i ≠ 0} := by
  simpa using affineZariski_polynomial_nonzero_open (X i)

theorem affineZariski_both_coordinates_nonzero_open :
    IsOpen {v : Fin 2 → ℂ | v 0 ≠ 0 ∧ v 1 ≠ 0} :=
  (affineZariski_coordinate_nonzero_open 0).inter (affineZariski_coordinate_nonzero_open 1)

/-- The induced topology has precisely the usual algebraic closure operator:
closure is the common zero set of all polynomials vanishing on the set.
Thus no closure claim is hidden in the choice of topology. -/
theorem affineZariski_closure (S : Set (Fin 2 → ℂ)) :
    closure S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} := by
  rw [affineZariski_embedding.closure_eq_preimage_closure_image,
    ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    spectrum_vanishingIdeal_image]
  rfl

/-- The previous spectral closure theorem now gives an actual closure theorem
on complex coordinate points with their Zariski topology. -/
theorem affineZariski_real_diagonal_closure {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    closure (affineRealDiagonal P) = {v : Fin 2 → ℂ | eval v P = 0} := by
  rw [affineZariski_embedding.closure_eq_preimage_closure_image,
    real_diagonal_spectrum_closure hP hinf]
  ext v
  change (∀ f ∈ ({P} : Set BPoly), eval v f = 0) ↔ eval v P = 0
  simp

#print axioms affineZariski_embedding
#print axioms affineZariski_closure
#print axioms affineZariski_real_diagonal_closure

end
end CurveSymmetry
