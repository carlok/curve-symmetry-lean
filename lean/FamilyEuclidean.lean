import FamilySphereClassification
import IsometryInterface

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section

/-- An affine map as an actual ambient Möbius transformation. -/
def affineMobiusMatrix (a b : ℂ) (ha : a ≠ 0) : MobiusMatrix :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1]
    (by simpa [Matrix.det_fin_two] using ha)

theorem affineMobiusMatrix_finite (a b : ℂ) (ha : a ≠ 0) (z : ℂ) :
    affineMobiusMatrix a b ha • (z : Sphere) = ((a * z + b : ℂ) : Sphere) := by
  simp [mobius_finite_formula, affineMobiusMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem affineMobiusMatrix_infinity (a b : ℂ) (ha : a ≠ 0) :
    affineMobiusMatrix a b ha • (∞ : Sphere) = ∞ := by
  simp [mobius_infinity_formula, affineMobiusMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- Even one-sided conjugate-affine preservation is impossible, including
the quartic case m=2. No isometry or unit-norm hypothesis on a is needed. -/
theorem family_no_conjugate_affine {m : ℕ} (hm : 2 ≤ m) {α a b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (ha0 : a ≠ 0) :
    ¬ (∀ z ∈ extremalCurve m α, a * star z + b ∈ extremalCurve m α) := by
  intro hf
  apply family_no_anti_mobius_self hm ha hα (affineMobiusMatrix a b ha0)
  intro p hp
  cases p using OnePoint.rec with
  | infty =>
    simpa [affineMobiusMatrix_infinity] using
      infinity_mem_sphericalFamily (by omega : 0 < m) ha
  | coe z =>
    have hz := (finite_mem_sphericalFamily_iff (by omega) ha z).mp hp
    simpa [affineMobiusMatrix_finite] using
      (finite_mem_sphericalFamily_iff (by omega) ha (a * star z + b)).mpr (hf z hz)

/-- Normalized family members have no opposite Euclidean symmetry for all
m>=2. The older unnormalized result for m>=3 remains available. -/
theorem family_no_opposite_normalized {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    IsEmpty (OppositeSymmetries (familyPolynomial m α)) := by
  refine ⟨fun g => ?_⟩
  have hga : g.val.1 ≠ 0 := by
    intro hz
    have hn := g.property.1
    simp [hz] at hn
  apply family_no_conjugate_affine hm ha hα hga
  intro z hz
  rw [← family_locus_eq] at hz ⊢
  exact (g.property.2 z).mpr hz

/-- Every actual Euclidean self-isometry is direct, including m=2.
The translation coefficient is not yet eliminated by this endpoint. -/
theorem family_isometry_direct {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : ℂ ≃ᵢ ℂ)
    (hf : ∀ z ∈ extremalCurve m α, f z ∈ extremalCurve m α) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z, f z = a * z + b := by
  rcases isometry_affine_forms f with h | ⟨a, b, hn, he⟩
  · exact h
  · have ha0 : a ≠ 0 := by intro hz; simp [hz] at hn
    exact False.elim (family_no_conjugate_affine hm ha hα ha0
      (fun z hz => (he z) ▸ hf z hz))

/-- Affine self-inclusion forces a centered root rotation. -/
theorem family_affine_self_filter {m : ℕ} (hm : 2 ≤ m) {α a b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (ha0 : a ≠ 0)
    (hf : ∀ z ∈ extremalCurve m α, a * z + b ∈ extremalCurve m α) :
    b = 0 ∧ a ^ (2 * m) = 1 := by
  have hs : ∀ p ∈ sphericalFamily m α,
      affineMobiusMatrix a b ha0 • p ∈ sphericalFamily m α := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => simpa [affineMobiusMatrix_infinity] using
        infinity_mem_sphericalFamily (by omega : 0 < m) ha
    | coe z =>
      simpa [affineMobiusMatrix_finite] using
        (finite_mem_sphericalFamily_iff (by omega) ha (a * z + b)).mpr
          (hf z ((finite_mem_sphericalFamily_iff (by omega) ha z).mp hp))
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ :=
    (family_mobius_self_filter hm ha hα (affineMobiusMatrix a b ha0)).mp hs
  · have h0 := he ((0 : ℂ) : Sphere)
    have h1 := he ((1 : ℂ) : Sphere)
    have hb : b = 0 := by simpa [affineMobiusMatrix_finite, sphereDilation] using h0
    have hac : a = c := by simpa [affineMobiusMatrix_finite, sphereDilation, hb] using h1
    exact ⟨hb, hac ▸ hr⟩
  · have hi := he ∞
    simp [affineMobiusMatrix_infinity, sphereInversion] at hi

/-- Exact characterization of actual Euclidean self-isometries. -/
theorem family_isometry_iff_rotation {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : ℂ ≃ᵢ ℂ) :
    (∀ z, f z ∈ extremalCurve m α ↔ z ∈ extremalCurve m α) ↔
      ∃ a : ℂ, a ^ (2 * m) = 1 ∧ ∀ z, f z = a * z := by
  constructor
  · intro hf
    obtain ⟨a, b, hn, he⟩ := family_isometry_direct hm ha hα f
      (fun z hz => (hf z).mpr hz)
    have ha0 : a ≠ 0 := by intro hz; simp [hz] at hn
    obtain ⟨hb, hr⟩ := family_affine_self_filter hm ha hα ha0
      (fun z hz => (he z) ▸ (hf z).mpr hz)
    exact ⟨a, hr, fun z => by simpa [hb] using he z⟩
  · rintro ⟨a, hr, he⟩ z
    have hs := family_root_symmetry (by omega : 0 < m) hr α
    rw [he, ← family_locus_eq]
    simpa only [add_zero] using hs.2 z

/-- The full group of actual Euclidean isometries has exactly 2m elements. -/
theorem family_isometry_card {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nat.card (isometrySetGroup (extremalCurve m α)) = 2 * m := by
  let := family_no_opposite_normalized hm ha hα
  rw [← family_locus_eq, ← Nat.card_congr (euclideanIsometryEquiv (familyPolynomial m α))]
  change Nat.card (DirectSymmetries (familyPolynomial m α) ⊕
    OppositeSymmetries (familyPolynomial m α)) = _
  rw [Nat.card_congr (Equiv.sumEmpty _ _)]
  exact family_direct_card hm ha

#print axioms family_affine_self_filter
#print axioms family_isometry_iff_rotation
#print axioms family_isometry_card
#print axioms family_no_conjugate_affine
#print axioms family_no_opposite_normalized
#print axioms family_isometry_direct

end
end CurveSymmetry
