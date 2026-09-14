import PaperBounds

namespace CurveSymmetry

set_option autoImplicit false

/-- The basic geometric clause of Theorem 2, including the quartic case m=2.
The equation is real Cartesian and geometrically irreducible over the complex
numbers; its actual locus is the displayed family. No unit-modulus restriction
on the nonreal parameter is needed. -/
theorem paper_family_geometry {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    ∃ f : RPoly, GeometricallyIrreducible f ∧ f.totalDegree = m + 2 ∧
      cartesianLocus f = extremalCurve m α ∧ (cartesianLocus f).Infinite := by
  have hm0 : 0 < m := by omega
  have hP := familyPolynomial_irreducible hm0 ha
  have hdeg := family_degree hm0 α
  have hinf := family_realLocus_infinite hm0 ha
  obtain ⟨f, hf, hfd, hfl⟩ := exists_cartesian_equation hP (by omega) hinf
  exact ⟨f, hf, hfd.trans hdeg, hfl.trans (family_locus_eq m α), hfl ▸ hinf⟩

#print axioms paper_family_geometry

end CurveSymmetry
