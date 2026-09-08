import MixedCornerClosure

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

lemma coordinate_one_irreducible : Irreducible (X 1 : BPoly) := by
  have h := coordinate_zero_irreducible.map
    (renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toMulEquiv
  change Irreducible (rename (Equiv.swap (0 : Fin 2) 1) (X 0 : BPoly)) at h
  simpa using h

lemma infinity_not_dvd_coordinates {m : ℕ} (hm : 0 < m) (α : ℂ) :
    ¬ (X 0 : BPoly) ∣ familyInfinityPolynomial m α ∧
    ¬ (X 1 : BPoly) ∣ familyInfinityPolynomial m α := by
  constructor
  · rintro ⟨Q, he⟩
    have h := congrArg (planeEval 0 1) he
    simp [familyInfinityPolynomial, fourTermForm, binaryForm, hm.ne'] at h
  · rintro ⟨Q, he⟩
    have h := congrArg (planeEval 1 0) he
    simp [familyInfinityPolynomial, fourTermForm, binaryForm, hm.ne'] at h

/-- Both reciprocal coordinates can be required to be nonzero: the actual
complex points of that open set are dense in the entire reciprocal chart curve.
No smoothness or irreducibility of the curve is assumed. -/
theorem reciprocal_chart_complex_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
      eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyInfinityPolynomial m α} : Set BPoly) := by
  have hn := infinity_not_dvd_coordinates hm α
  have he : {v : Fin 2 → ℂ |
      eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0} =
      {v : Fin 2 → ℂ | eval v (familyInfinityPolynomial m α) = 0 ∧
        eval v (X 0 * X 1) ≠ 0} := by simp
  rw [he]
  apply complex_points_deleted_divisor_closure
  · intro h; exact hn.1 (h ▸ dvd_zero _)
  · intro q hq hqF hd
    rcases hq.prime.dvd_mul.mp hd with h0 | h1
    · exact hn.1 ((hq.associated_of_dvd coordinate_zero_irreducible h0).symm.dvd.trans hqF)
    · exact hn.2 ((hq.associated_of_dvd coordinate_one_irreducible h1).symm.dvd.trans hqF)

/-- The reciprocal-chart origin, representing `(∞,∞)`, belongs to the
Zariski closure of complex chart points for which both original coordinates
are finite. Projective chart gluing remains a separate obligation. -/
theorem reciprocal_corner_mem_complex_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
        eval v (familyInfinityPolynomial m α) = 0 ∧ v 0 ≠ 0 ∧ v 1 ≠ 0}) := by
  rw [reciprocal_chart_complex_closure hm α]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyInfinityPolynomial m α) = 0
  simp [familyInfinityPolynomial, fourTermForm, binaryForm, hm.ne']

#print axioms reciprocal_chart_complex_closure
#print axioms reciprocal_corner_mem_complex_closure

end CurveSymmetry
