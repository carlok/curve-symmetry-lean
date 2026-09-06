import FamilyProjective

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

noncomputable def mobiusX (g : MobiusMatrix) (i : Fin 2) : BPoly :=
  C (g i 0) * X 0 + C (g i 1)

noncomputable def mobiusY (g : MobiusMatrix) (i : Fin 2) : BPoly :=
  C (star (g i 0)) * X 1 + C (star (g i 1))

/-- The actual denominator-cleared pullback for an arbitrary invertible matrix.
No preservation of the singular pair or special matrix form is assumed. -/
noncomputable def familyMobiusPullback (m : ℕ) (β : ℂ) (g : MobiusMatrix) : BPoly :=
  C β * mobiusX g 0 ^ m * mobiusX g 1 * mobiusY g 1 ^ (m + 1) +
  mobiusX g 0 ^ (m + 1) * mobiusY g 0 * mobiusY g 1 ^ m +
  C (star β) * mobiusX g 1 ^ (m + 1) * mobiusY g 0 ^ m * mobiusY g 1 +
  mobiusX g 0 * mobiusX g 1 ^ m * mobiusY g 0 ^ (m + 1)

lemma familyMobiusPullback_eval (m : ℕ) (β x y : ℂ) (g : MobiusMatrix) :
    planeEval x y (familyMobiusPullback m β g) =
      familyBihomogeneous m β (g • ![x, 1]) ((g.map (starRingEnd ℂ)) • ![y, 1]) := by
  simp [familyMobiusPullback, mobiusX, mobiusY, familyBihomogeneous,
    Matrix.GeneralLinearGroup.fin_two_smul]

theorem familyMobiusPullback_projective_iff (m : ℕ) (β x y : ℂ) (g : MobiusMatrix) :
    complexifiedMobius g (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (y : Sphere)) ∈
      familyProjectiveCurve m β ↔ planeEval x y (familyMobiusPullback m β g) = 0 := by
  change (g • sphereProjectiveEquiv (x : Sphere),
    (g.map (starRingEnd ℂ)) • sphereProjectiveEquiv (y : Sphere)) ∈ _ ↔ _
  rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_finite,
    Projectivization.smul_mk, Projectivization.smul_mk, familyProjective_mk_iff,
    familyMobiusPullback_eval]

/-- Spherical real-locus inclusion already forces divisibility by the source
equation, even when the matrix has poles on the curve. Nonzero scalar
proportionality and singularity transport are still separate obligations. -/
theorem family_dvd_mobiusPullback {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    familyPolynomial m α ∣ familyMobiusPullback m β g := by
  apply dvd_of_realLocus_subset (familyPolynomial_irreducible hm ha)
    (family_realLocus_infinite hm ha)
  intro z hz
  have hzSphere : (z : Sphere) ∈ sphericalFamily m α := by
    rw [finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq]
    exact hz
  have ht := (sphericalFamily_projective_iff hm hb (g • (z : Sphere))).mpr
    (hmap (z : Sphere) hzSphere)
  rw [sphereRealDiagonal_action] at ht
  change planeEval z (star z) (familyMobiusPullback m β g) = 0
  exact (familyMobiusPullback_projective_iff m β z (star z) g).mp ht

#print axioms familyMobiusPullback_projective_iff
#print axioms family_dvd_mobiusPullback

end CurveSymmetry
