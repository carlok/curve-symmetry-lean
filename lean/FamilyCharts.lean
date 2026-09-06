import FamilySingularities
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- Clearing the two inversion denominators gives the reciprocal chart equation. -/
lemma family_reciprocal_chart (m : ℕ) (α : ℂ) {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    (u * v) ^ (m + 1) * planeEval u⁻¹ v⁻¹ (familyPolynomial m α) =
      planeEval u v (familyInfinityPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval, familyInfinityPolynomial, fourTermForm_eval]
  simp only [mul_pow, pow_succ, inv_pow, one_mul]
  field_simp
  ring

noncomputable def familyMixedPolynomial (m : ℕ) (a b : ℂ) : BPoly :=
  C a * X 0 + X 1 + C b * X 0 ^ (m + 1) * X 1 ^ m + X 0 ^ m * X 1 ^ (m + 1)

/-- The chart with `u=1/X` and `Y` unchanged. -/
lemma family_mixed_chart (m : ℕ) (α : ℂ) {u y : ℂ} (hu : u ≠ 0) :
    u ^ (m + 1) * planeEval u⁻¹ y (familyPolynomial m α) =
      planeEval u y (familyMixedPolynomial m α (star α)) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyMixedPolynomial, map_add, map_mul, map_pow, planeEval_C,
    planeEval_X_zero, planeEval_X_one, pow_succ, inv_pow, one_mul]
  field_simp
  ring

/-- The other mixed chart, written in coordinates `v=1/Y` and `X`. -/
lemma family_other_mixed_chart (m : ℕ) (α : ℂ) {x v : ℂ} (hv : v ≠ 0) :
    v ^ (m + 1) * planeEval x v⁻¹ (familyPolynomial m α) =
      planeEval v x (familyMixedPolynomial m (star α) α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyMixedPolynomial, map_add, map_mul, map_pow, planeEval_C,
    planeEval_X_zero, planeEval_X_one, pow_succ, inv_pow, one_mul]
  field_simp
  ring

/-- Both mixed boundary corners are smooth: the indicated partial derivative is `1`. -/
lemma family_mixed_partial (m : ℕ) (hm : 0 < m) (a b : ℂ) :
    planeEval 0 0 (pderiv 1 (familyMixedPolynomial m a b)) = 1 := by
  simp [familyMixedPolynomial, hm.ne']

theorem family_mixed_not_singular {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    ¬ JacobianSingular (familyMixedPolynomial m a b) 0 0 := by
  intro hs
  have he := hs.2.2
  rw [family_mixed_partial m hm] at he
  exact one_ne_zero he

/-- The one-variable tangent-direction polynomial has no repeated root.
This is the algebraic ingredient for ordinary multiple points, not yet an
interface to the singularity or normalization of a projective scheme. -/
theorem binary_tangent_separable {m : ℕ} (hm : 0 < m) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Polynomial.Separable (Polynomial.C a * Polynomial.X ^ m + Polynomial.C b) := by
  have he : Polynomial.C a * Polynomial.X ^ m + Polynomial.C b =
      (Polynomial.X ^ m - Polynomial.C (-b / a)) * Polynomial.C a := by
    rw [sub_mul, ← Polynomial.C_mul]
    have heq : -b / a * a = -b := div_mul_cancel₀ _ ha
    rw [heq, Polynomial.C_neg]
    ring
  rw [he]
  apply Polynomial.Separable.mul_unit
  · apply Polynomial.separable_X_pow_sub_C
    · exact_mod_cast hm.ne'
    · exact div_ne_zero (neg_ne_zero.mpr hb) ha
  · exact (isUnit_iff_ne_zero.mpr ha).map Polynomial.C

lemma binaryForm_homogeneous (m : ℕ) (a b : ℂ) : (binaryForm m a b).IsHomogeneous m :=
  (isHomogeneous_C_mul_X_pow a 0 m).add (isHomogeneous_C_mul_X_pow b 1 m)

lemma fourTermForm_components (m n : ℕ) (a b c d : ℂ) :
    homogeneousComponent n (fourTermForm m a b c d) =
      (if n = m then binaryForm m a b else 0) +
        (if n = m + 2 then X 0 * X 1 * binaryForm m c d else 0) := by
  have hhigh : (X 0 * X 1 * binaryForm m c d).IsHomogeneous (m + 2) := by
    convert ((isHomogeneous_X ℂ (0 : Fin 2)).mul (isHomogeneous_X ℂ 1)).mul
      (binaryForm_homogeneous m c d) using 1
    omega
  rw [fourTermForm, map_add, homogeneousComponent_of_mem (binaryForm_homogeneous m a b),
    homogeneousComponent_of_mem hhigh]

/-- Exact lowest-degree component and its separable dehomogenization.
Both diagonal charts therefore have the ordinary-point tangent-cone data. -/
theorem fourTermForm_tangent_data {m : ℕ} (hm : 0 < m) {a b : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (c d : ℂ) :
    (∀ n < m, homogeneousComponent n (fourTermForm m a b c d) = 0) ∧
      homogeneousComponent m (fourTermForm m a b c d) = binaryForm m a b ∧
      binaryForm m a b ≠ 0 ∧
      Polynomial.Separable (Polynomial.C a * Polynomial.X ^ m + Polynomial.C b) := by
  refine ⟨?_, ?_, ?_, binary_tangent_separable hm ha hb⟩
  · intro n hn
    rw [fourTermForm_components, if_neg (by omega), if_neg (by omega), add_zero]
  · rw [fourTermForm_components, if_pos rfl, if_neg (by omega), add_zero]
  · intro hz
    have he := congrArg (planeEval 1 0) hz
    simp [binaryForm, hm.ne'] at he
    exact ha he

#print axioms family_reciprocal_chart
#print axioms family_mixed_chart
#print axioms family_other_mixed_chart
#print axioms family_mixed_not_singular
#print axioms binary_tangent_separable
#print axioms fourTermForm_tangent_data

end CurveSymmetry
