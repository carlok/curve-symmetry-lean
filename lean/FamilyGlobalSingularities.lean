import HomogeneousCharts
import MobiusPair

namespace CurveSymmetry

set_option autoImplicit false
open OnePoint

lemma familyProjectiveCritical_subset (m : ℕ) (α : ℂ) :
    familyProjectiveCritical m α ⊆ familyProjectiveCurve m α := fun _ h => h.1

lemma family_critical_infinity_finite_false {m : ℕ} (hm : 0 < m) (α y : ℂ) :
    (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (y : Sphere)) ∉
      familyProjectiveCritical m α := by
  intro h
  have hy := (familyProjective_infinity_finite hm α y).mp
    (familyProjectiveCritical_subset m α h)
  subst y
  rw [sphereProjectiveEquiv_infinity, sphereProjectiveEquiv_finite,
    familyProjectiveCritical_mk_iff, family_critical_mixed_iff] at h
  exact family_mixed_not_singular hm α (star α) h

/-- Exact classification of the global homogeneous Jacobian locus on the
constructed product-projective curve, including every boundary point. -/
theorem family_projective_critical_pair {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (p q : Sphere) :
    (sphereProjectiveEquiv p, sphereProjectiveEquiv q) ∈ familyProjectiveCritical m α ↔
      (p = (0 : ℂ) ∧ q = (0 : ℂ)) ∨ (p = ∞ ∧ q = ∞) := by
  have hm0 : 0 < m := by omega
  cases p using OnePoint.rec with
  | infty =>
      cases q using OnePoint.rec with
      | infty =>
          rw [sphereProjectiveEquiv_infinity, familyProjectiveCritical_mk_iff,
            family_critical_reciprocal_iff, family_infinity_singular_iff hm ha]
          simp
      | coe y =>
          simp [family_critical_infinity_finite_false hm0 α y]
  | coe x =>
      cases q using OnePoint.rec with
      | infty =>
          have hn : (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∉
              familyProjectiveCritical m α := by
            intro h
            have hs := (family_projective_critical_swap m (star α)
              (sphereProjectiveEquiv (x : Sphere), sphereProjectiveEquiv (∞ : Sphere))).mpr
              (by simpa only [star_star] using h)
            exact family_critical_infinity_finite_false hm0 (star α) x hs
          simp [hn]
      | coe y =>
          rw [sphereProjectiveEquiv_finite, sphereProjectiveEquiv_finite,
            familyProjectiveCritical_mk_iff, family_critical_affine_iff,
            family_affine_singular_iff hm ha]
          simp

theorem family_projective_critical_eq_pair {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) :
    familyProjectiveCritical m α =
      {(sphereProjectiveEquiv ((0 : ℂ) : Sphere), sphereProjectiveEquiv ((0 : ℂ) : Sphere)),
        (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere))} := by
  ext ⟨p, q⟩
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  obtain ⟨v, rfl⟩ := sphereProjectiveEquiv.surjective q
  rw [family_projective_critical_pair hm ha]
  simp

lemma family_diagonal_critical_iff {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (p : Sphere) :
    sphereRealDiagonal p ∈ familyProjectiveCritical m α ↔
      p ∈ ({((0 : ℂ) : Sphere), ∞} : Set Sphere) := by
  rw [sphereRealDiagonal, family_projective_critical_pair hm ha]
  constructor
  · rintro (h | h)
    · simp [h.1]
    · simp [h.1]
  · intro hp
    rcases (by simpa using hp : p = ((0 : ℂ) : Sphere) ∨ p = ∞) with rfl | rfl <;> simp

/-- Preservation of the singular pair is a consequence of actual spherical
containment, not a hypothesis of the completeness theorem. -/
theorem family_mobius_preserves_pair {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    (fun p : Sphere => g • p) '' {((0 : ℂ) : Sphere), ∞} = {((0 : ℂ) : Sphere), ∞} := by
  have hm0 : 0 < m := by omega
  have hi (p : Sphere) : g • p ∈ ({((0 : ℂ) : Sphere), ∞} : Set Sphere) ↔
      p ∈ ({((0 : ℂ) : Sphere), ∞} : Set Sphere) := by
    rw [← family_diagonal_critical_iff hm hb, sphereRealDiagonal_action,
      family_mobius_projective_critical_transport hm0 ha hb g hmap,
      family_diagonal_critical_iff hm ha]
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact (hi q).mpr hq
  · intro hp
    refine ⟨g⁻¹ • p, (hi (g⁻¹ • p)).mp ?_, by simp⟩
    simpa using hp

/-- Completeness for arbitrary ambient Möbius maps. The two forms hold on the
whole sphere, including zero and infinity, and pair preservation is derived. -/
theorem family_mobius_complete {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ p : Sphere, g • p = sphereDilation c p) ∨
      (∀ p : Sphere, g • p = sphereInversion c p)) :=
  mobius_forms_of_preserves_pair g (family_mobius_preserves_pair hm ha hb g hmap)

/-- The antiholomorphic completeness statement, with conjugation explicit in
the actual sphere action. No restriction on the matrix form is assumed. -/
theorem family_anti_mobius_complete {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((∀ p : Sphere, g • OnePoint.map (star : ℂ → ℂ) p =
        sphereDilation c (OnePoint.map (star : ℂ → ℂ) p)) ∨
      (∀ p : Sphere, g • OnePoint.map (star : ℂ → ℂ) p =
        sphereInversion c (OnePoint.map (star : ℂ → ℂ) p))) := by
  have hm0 : 0 < m := by omega
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  have hhol : ∀ q ∈ sphericalFamily m (star α), g • q ∈ sphericalFamily m β := by
    intro q hq
    have hconj := (conjugate_mem_sphericalFamily_iff hm0 ha q).mpr hq
    simpa only [sphere_conjugation_involutive] using
      hmap (OnePoint.map (star : ℂ → ℂ) q) hconj
  obtain ⟨c, hc, he | he⟩ := family_mobius_complete hm has hb g hhol
  · exact ⟨c, hc, Or.inl (fun p => he (OnePoint.map (star : ℂ → ℂ) p))⟩
  · exact ⟨c, hc, Or.inr (fun p => he (OnePoint.map (star : ℂ → ℂ) p))⟩

#print axioms family_projective_critical_pair
#print axioms family_projective_critical_eq_pair
#print axioms family_mobius_preserves_pair
#print axioms family_mobius_complete
#print axioms family_anti_mobius_complete

end CurveSymmetry
