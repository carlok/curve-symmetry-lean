import FamilySphereDilation
import FamilySphereInversion
import FamilyGlobalSingularities

namespace CurveSymmetry

set_option autoImplicit false

/-- Exact coefficient and map-form test for an arbitrary ambient Möbius
matrix, on all sphere points. The input is inclusion, not assumed equality. -/
theorem family_mobius_self_filter {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix) :
    (∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) ↔
      ∃ c : ℂ, c ≠ 0 ∧
        ((c ^ (2 * m) = 1 ∧ ∀ p : Sphere, g • p = sphereDilation c p) ∨
         (c ^ (2 * m) = star α ^ 2 ∧ ∀ p : Sphere, g • p = sphereInversion c p)) := by
  have hm0 : 0 < m := by omega
  constructor
  · intro hmap
    obtain ⟨c, hc, he | he⟩ := family_mobius_complete hm ha ha g hmap
    · exact ⟨c, hc, Or.inl ⟨(family_sphere_dilation_filter hm0 ha hα hc).mp
        (fun p hp => (he p) ▸ hmap p hp), he⟩⟩
    · exact ⟨c, hc, Or.inr ⟨(family_sphere_inversion_filter hm0 hα ha hc).mp
        (fun p hp => (he p) ▸ hmap p hp), he⟩⟩
  · rintro ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ p hp
    · rw [he]
      exact (family_sphere_dilation_filter hm0 ha hα hc).mpr hr p hp
    · rw [he]
      exact (family_sphere_inversion_filter hm0 hα ha hc).mpr hr p hp

/-- One-sided self-inclusion is already exact membership preservation. -/
theorem family_mobius_self_mem_iff {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) (p : Sphere) :
    g • p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ := (family_mobius_self_filter hm ha hα g).mp hmap
  · rw [he]
    exact family_sphere_dilation_mem_iff (by omega) ha hα hc hr p
  · rw [he]
    exact family_sphere_inversion_mem_iff (by omega) hα ha hc hr p

theorem family_mobius_parameter_necessary {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) : β = α := by
  obtain ⟨c, hc, he | he⟩ := family_mobius_complete hm ha hb g hmap
  · exact (family_sphere_dilation_parameter (by omega) ha hb hα hβ hc
      (fun p hp => (he p) ▸ hmap p hp)).2
  · exact (family_sphere_inversion_parameter (by omega) hα hβ ha hb hc
      (fun p hp => (he p) ▸ hmap p hp)).2

theorem family_anti_mobius_parameter_necessary {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β) : β = star α := by
  apply family_mobius_parameter_necessary hm (by simpa only [star_star, ne_comm] using ha)
    hb (by simpa using hα) hβ g
  intro q hq
  have hconj := (conjugate_mem_sphericalFamily_iff (by omega) ha q).mpr hq
  simpa only [sphere_conjugation_involutive] using
    hmap (OnePoint.map (star : ℂ → ℂ) q) hconj

/-- No anti-Möbius self-inclusion, hence in particular no anti-Möbius symmetry. -/
theorem family_no_anti_mobius_self {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (g : MobiusMatrix) :
    ¬ (∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m α) := by
  intro hmap
  exact ha (family_anti_mobius_parameter_necessary hm ha ha hα hα g hmap)

/-- Complete holomorphic parameter classification using equality of the actual
spherical loci under an ambient Möbius transformation. -/
theorem family_mobius_equivalence_iff {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) :
    (∃ g : MobiusMatrix, (fun p : Sphere => g • p) '' sphericalFamily m α =
      sphericalFamily m β) ↔ β = α := by
  constructor
  · rintro ⟨g, hg⟩
    apply family_mobius_parameter_necessary hm ha hb hα hβ g
    intro p hp
    rw [← hg]
    exact ⟨p, hp, rfl⟩
  · rintro rfl
    exact ⟨1, by simp⟩

/-- Complete antiholomorphic parameter classification; conjugation supplies
the reverse implication, including its action at infinity. -/
theorem family_anti_mobius_equivalence_iff {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) :
    (∃ g : MobiusMatrix,
      (fun p : Sphere => g • OnePoint.map (star : ℂ → ℂ) p) '' sphericalFamily m α =
        sphericalFamily m β) ↔ β = star α := by
  constructor
  · rintro ⟨g, hg⟩
    apply family_anti_mobius_parameter_necessary hm ha hb hα hβ g
    intro p hp
    rw [← hg]
    exact ⟨p, hp, rfl⟩
  · rintro rfl
    refine ⟨1, ?_⟩
    simp only [one_smul]
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      apply (conjugate_mem_sphericalFamily_iff (by omega) ha
        (OnePoint.map (star : ℂ → ℂ) p)).mp
      simpa only [sphere_conjugation_involutive] using hp
    · intro hq
      exact ⟨OnePoint.map (star : ℂ → ℂ) q,
        (conjugate_mem_sphericalFamily_iff (by omega) ha q).mpr hq,
        sphere_conjugation_involutive q⟩

#print axioms family_mobius_equivalence_iff
#print axioms family_anti_mobius_equivalence_iff
#print axioms family_mobius_self_filter
#print axioms family_mobius_parameter_necessary
#print axioms family_no_anti_mobius_self

end CurveSymmetry
