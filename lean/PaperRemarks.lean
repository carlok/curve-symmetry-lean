import FermatGenus

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
* `paper_degree_four_genus`: Remark 5 as printed, "genera three versus two". The
  function field of `Re(z⁴) = 1` (complexified: `X⁴ + Y⁴ = 2`) has genus exactly
  three, every `m = 2` family curve has genus two, and the non-similarity above.
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

/-- `m = 2` in the family's instances. -/
local instance fact_zero_lt_two : Fact (0 < 2) :=
  ⟨by norm_num⟩

/-- **Remark 5, degree four, as printed**: `Re(z⁴) = 1` has the maximal four rotations, its
function field has genus three, every curve of the `m = 2` family has genus two, and no
similarity, direct or orientation-reversing, carries the first onto the second. -/
theorem paper_degree_four_genus :
    Nat.card (directIsometryGroup {z : ℂ | (z ^ 4).re = 1}) = 4 ∧
      genus (FermatFunctionField 4) = 3 ∧
      (∀ (α : ℂ) [Fact (α ≠ star α)], genus (FamilyFunctionField 2 α) = 2) ∧
      ¬ ∃ a b α : ℂ, a ≠ 0 ∧ α ≠ star α ∧
        ((fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α ∨
          (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} = extremalCurve 2 α) := by
  obtain ⟨hcard, hnot⟩ := paper_degree_four_not_in_family
  exact ⟨hcard, fermatFunctionField_genus, fun _ _ => paper_family_genus, hnot⟩

#print axioms paper_family_genus
#print axioms paper_degree_four_not_in_family
#print axioms paper_degree_four_genus

end CurveSymmetry
