import QuarticComparison

/-!
# Paper-facing statements for Lemma 4's genus and Remark 5 (R01)

Kept apart from `PaperBounds` so that the import closure of the Theorem 1
Palomar entry does not change.

* `paper_family_genus`: Lemma 4's genus clause at the approved reading. The
  function field of the family curve, `Frac(ℂ[X,Y]/(P_α))`, has genus `m`: its
  holomorphic differentials, those regular at every place, have dimension `m`.
* `paper_degree_four_not_in_family`: Remark 5 in degree four. `Re(z⁴) = 1`
  attains the rotation bound `max(4, 2·4 − 4) = 4`, and no similarity, direct or
  orientation-reversing, carries it onto a curve of the `m = 2` family, because
  its function field has three independent holomorphic differentials and the
  family's has genus two. The parameter only needs to be nonreal.

That the quartic's genus is exactly three is R01e.
-/

namespace CurveSymmetry

set_option autoImplicit false

/-- **Lemma 4, genus clause**: the function field of the family curve has genus `m`. -/
theorem paper_family_genus {m : ℕ} [Fact (0 < m)] {α : ℂ} [Fact (α ≠ star α)] :
    genus (FamilyFunctionField m α) = m :=
  familyFunctionField_genus

/-- **Remark 5, degree four**: `Re(z⁴) = 1` has the maximal four rotations, and no similarity
carries it onto a curve of the `m = 2` family. -/
theorem paper_degree_four_not_in_family :
    Nat.card (directIsometryGroup {z : ℂ | (z ^ 4).re = 1}) = 4 ∧
      ¬ ∃ a b α : ℂ, a ≠ 0 ∧ α ≠ star α ∧
        ((fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α ∨
          (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α) := by
  refine ⟨?_, ?_⟩
  · rw [← realLocus_fermat_four, ← Nat.card_congr (directIsometryEquiv (fermatPolynomial 4))]
    exact fermat_direct_card (by norm_num)
  · rintro ⟨a, b, α, ha, hα, hS | hS⟩
    · exact quartic_not_similar_family hα ha hS
    · exact quartic_not_oppositeSimilar_family hα ha hS

#print axioms paper_family_genus
#print axioms paper_degree_four_not_in_family

end CurveSymmetry
