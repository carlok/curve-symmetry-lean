import SphereGeometry
import FamilyCharts

namespace CurveSymmetry

set_option autoImplicit false
open OnePoint

abbrev ProjectiveLine := Projectivization ℂ (Fin 2 → ℂ)

/-- The bihomogeneous equation in two pairs of homogeneous coordinates.
On `x=[X:1]`, `y=[Y:1]` this is precisely `familyPolynomial m α`. -/
def familyBihomogeneous (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ) : ℂ :=
  α * x 0 ^ m * x 1 * y 1 ^ (m + 1) +
  x 0 ^ (m + 1) * y 0 * y 1 ^ m +
  star α * x 1 ^ (m + 1) * y 0 ^ m * y 1 +
  x 0 * x 1 ^ m * y 0 ^ (m + 1)

lemma familyBihomogeneous_smul_left (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α (a • x) y = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring

lemma familyBihomogeneous_smul_right (m : ℕ) (α a : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α x (a • y) = a ^ (m + 1) * familyBihomogeneous m α x y := by
  simp only [familyBihomogeneous, Pi.smul_apply, smul_eq_mul, mul_pow, pow_succ]
  ring

/-- The bihomogeneous zero locus on the standard product of projective lines.
The next lemma proves that its meaning does not depend on chosen representatives.
Its identification with the Zariski closure is a separate pending obligation. -/
def familyProjectiveCurve (m : ℕ) (α : ℂ) : Set (ProjectiveLine × ProjectiveLine) :=
  {p | familyBihomogeneous m α p.1.rep p.2.rep = 0}

theorem familyProjective_mk_iff (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈ familyProjectiveCurve m α ↔
      familyBihomogeneous m α x y = 0 := by
  change familyBihomogeneous m α (Projectivization.mk ℂ x hx).rep
    (Projectivization.mk ℂ y hy).rep = 0 ↔ _
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha, ← hb]
  simp [Units.smul_def, familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]

lemma familyBihomogeneous_affine (m : ℕ) (α x y : ℂ) :
    familyBihomogeneous m α ![x, 1] ![y, 1] = planeEval x y (familyPolynomial m α) := by
  rw [family_fourTerm, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one]
  ring

lemma familyBihomogeneous_reciprocal (m : ℕ) (α u v : ℂ) :
    familyBihomogeneous m α ![1, u] ![1, v] =
      planeEval u v (familyInfinityPolynomial m α) := by
  rw [familyInfinityPolynomial, fourTermForm_eval]
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, one_mul]
  ring

lemma familyBihomogeneous_mixed (m : ℕ) (α u y : ℂ) :
    familyBihomogeneous m α ![1, u] ![y, 1] =
      planeEval u y (familyMixedPolynomial m α (star α)) := by
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, one_mul, familyMixedPolynomial,
    map_add, map_mul, map_pow, planeEval_C, planeEval_X_zero, planeEval_X_one]

lemma familyBihomogeneous_other_mixed (m : ℕ) (α x v : ℂ) :
    familyBihomogeneous m α ![x, 1] ![1, v] =
      planeEval v x (familyMixedPolynomial m (star α) α) := by
  simp only [familyBihomogeneous, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, one_pow, mul_one, familyMixedPolynomial,
    map_add, map_mul, map_pow, planeEval_C, planeEval_X_zero, planeEval_X_one]
  ring

theorem familyProjective_affine_iff (m : ℕ) (α x y : ℂ) :
    (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (y : Sphere)) ∈
      familyProjectiveCurve m α ↔ planeEval x y (familyPolynomial m α) = 0 := by
  rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_finite, familyProjective_mk_iff,
    familyBihomogeneous_affine]

/-- The real sphere sits in the complexification by `p ↦ (p, conjugate p)`. -/
noncomputable def sphereRealDiagonal (p : Sphere) : ProjectiveLine × ProjectiveLine :=
  (sphereProjectiveEquiv p, sphereProjectiveEquiv (OnePoint.map (star : ℂ → ℂ) p))

/-- The ordinary product-projective extension of an arbitrary Möbius matrix. -/
noncomputable def complexifiedMobius (g : MobiusMatrix)
    (p : ProjectiveLine × ProjectiveLine) : ProjectiveLine × ProjectiveLine :=
  (g • p.1, (g.map (starRingEnd ℂ)) • p.2)

theorem sphereRealDiagonal_action (g : MobiusMatrix) (p : Sphere) :
    sphereRealDiagonal (g • p) = complexifiedMobius g (sphereRealDiagonal p) := by
  apply Prod.ext
  · exact sphereProjectiveEquiv_action g p
  · change sphereProjectiveEquiv (OnePoint.map (starRingEnd ℂ) (g • p)) =
      (g.map (starRingEnd ℂ)) • sphereProjectiveEquiv (OnePoint.map (starRingEnd ℂ) p)
    rw [OnePoint.map_smul, sphereProjectiveEquiv_action]

lemma sphereRealDiagonal_conjugate (p : Sphere) :
    sphereRealDiagonal (OnePoint.map (star : ℂ → ℂ) p) = (sphereRealDiagonal p).swap := by
  cases p using OnePoint.rec with
  | infty => rfl
  | coe z => simp [sphereRealDiagonal]

/-- For an anti-Möbius map, the two projective factors are exchanged first. -/
noncomputable def complexifiedAntiMobius (g : MobiusMatrix)
    (p : ProjectiveLine × ProjectiveLine) : ProjectiveLine × ProjectiveLine :=
  complexifiedMobius g p.swap

theorem sphereRealDiagonal_anti_action (g : MobiusMatrix) (p : Sphere) :
    sphereRealDiagonal (g • OnePoint.map (star : ℂ → ℂ) p) =
      complexifiedAntiMobius g (sphereRealDiagonal p) := by
  rw [sphereRealDiagonal_action, sphereRealDiagonal_conjugate]
  rfl

lemma familyProjective_infinity_finite {m : ℕ} (hm : 0 < m) (α y : ℂ) :
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (y : Sphere)) ∈
      familyProjectiveCurve m α ↔ y = 0 := by
  rw [sphereProjectiveEquiv_infinity, sphereProjectiveEquiv_finite, familyProjective_mk_iff]
  simp [familyBihomogeneous, hm.ne']

lemma familyProjective_finite_infinity {m : ℕ} (hm : 0 < m) (α x : ℂ) :
    (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∈
      familyProjectiveCurve m α ↔ x = 0 := by
  rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_infinity, familyProjective_mk_iff]
  simp [familyBihomogeneous, hm.ne']

lemma familyProjective_infinity_infinity {m : ℕ} (hm : 0 < m) (α : ℂ) :
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∈
      familyProjectiveCurve m α := by
  rw [sphereProjectiveEquiv_infinity, familyProjective_mk_iff]
  simp [familyBihomogeneous, hm.ne']

/-- The real part of the projective zero locus is exactly the genuine spherical
closure, including infinity. This is not yet Zariski-density or map transport. -/
theorem sphericalFamily_projective_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (p : Sphere) :
    sphereRealDiagonal p ∈ familyProjectiveCurve m α ↔ p ∈ sphericalFamily m α := by
  cases p using OnePoint.rec with
  | infty =>
    change (sphereProjectiveEquiv ∞, sphereProjectiveEquiv ∞) ∈ familyProjectiveCurve m α ↔ _
    exact iff_of_true (familyProjective_infinity_infinity hm α) (infinity_mem_sphericalFamily hm ha)
  | coe z =>
    change (sphereProjectiveEquiv (z : Sphere), sphereProjectiveEquiv ((star z : ℂ) : Sphere)) ∈
      familyProjectiveCurve m α ↔ _
    rw [familyProjective_affine_iff, finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq]
    rfl

#print axioms familyProjective_mk_iff
#print axioms familyProjective_affine_iff
#print axioms familyBihomogeneous_reciprocal
#print axioms sphericalFamily_projective_iff
#print axioms sphereRealDiagonal_action
#print axioms sphereRealDiagonal_anti_action

end CurveSymmetry
