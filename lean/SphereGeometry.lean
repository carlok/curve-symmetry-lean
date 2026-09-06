import PaperBounds
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

namespace CurveSymmetry

set_option autoImplicit false
open scoped LinearAlgebra.Projectivization
open OnePoint

/-- The ordinary one-point compactification of the complex plane. -/
abbrev Sphere := OnePoint ℂ

/-- Arbitrary invertible matrices, not just the anticipated classified forms. -/
abbrev MobiusMatrix := Matrix.GeneralLinearGroup (Fin 2) ℂ

/-- Mathlib's standard finite-chart/infinity identification with the projective line.
This is a set equivalence; no unproved projective-topology compatibility is asserted. -/
noncomputable def sphereProjectiveEquiv : Sphere ≃ Projectivization ℂ (Fin 2 → ℂ) :=
  OnePoint.equivProjectivization ℂ

lemma sphereProjectiveEquiv_finite (z : ℂ) :
    sphereProjectiveEquiv (z : Sphere) = Projectivization.mk ℂ ![z, 1] (by simp) := rfl

lemma sphereProjectiveEquiv_infinity :
    sphereProjectiveEquiv (∞ : Sphere) = Projectivization.mk ℂ ![1, 0] (by simp) := rfl

lemma sphereProjectiveEquiv_action (g : MobiusMatrix) (p : Sphere) :
    sphereProjectiveEquiv (g • p) = g • sphereProjectiveEquiv p :=
  OnePoint.equivProjectivization_smul p

lemma mobius_finite_formula (g : MobiusMatrix) (z : ℂ) :
    g • (z : Sphere) = if g 1 0 * z + g 1 1 = 0 then ∞
      else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) :=
  OnePoint.smul_some_eq_ite

lemma mobius_infinity_formula (g : MobiusMatrix) :
    g • (∞ : Sphere) = if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) :=
  OnePoint.smul_infty_eq_ite g

/-- Spherical closure has its ordinary topological meaning from the outset. -/
def sphericalFamily (m : ℕ) (α : ℂ) : Set Sphere :=
  closure (((↑) : ℂ → Sphere) '' extremalCurve m α)

lemma extremalCurve_isClosed (m : ℕ) (α : ℂ) : IsClosed (extremalCurve m α) := by
  apply isClosed_eq _ continuous_const
  fun_prop

lemma extremalCurve_not_isCompact {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    ¬ IsCompact (extremalCurve m α) := by
  intro hc
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  obtain ⟨z, hz, hn⟩ := family_point_of_norm hm ha
    (show 0 ≤ max R 0 + 1 by positivity)
  rw [family_locus_eq] at hz
  have hb := hR z hz
  rw [hn] at hb
  have hmax := le_max_left R 0
  linarith

/-- A closed noncompact plane set gains exactly infinity under spherical closure. -/
lemma closure_onePoint_image {S : Set ℂ} (hs : IsClosed S) (hnc : ¬ IsCompact S) :
    closure (((↑) : ℂ → Sphere) '' S) = insert ∞ (((↑) : ℂ → Sphere) '' S) := by
  have hclosed : IsClosed (insert ∞ (((↑) : ℂ → Sphere) '' S)) := by
    apply (OnePoint.isClosed_iff_of_mem (Set.mem_insert _ _)).mpr
    convert hs using 1
    ext z
    simp
  have hsub := closure_minimal (Set.subset_insert ∞ (((↑) : ℂ → Sphere) '' S)) hclosed
  have hinf : ∞ ∈ closure (((↑) : ℂ → Sphere) '' S) := by
    by_contra h
    have he : closure (((↑) : ℂ → Sphere) '' S) = ((↑) : ℂ → Sphere) '' S := by
      apply Set.Subset.antisymm _ subset_closure
      intro p hp
      rcases Set.mem_insert_iff.mp (hsub hp) with rfl | hp'
      · exact (h hp).elim
      · exact hp'
    exact hnc (OnePoint.isClosed_image_coe.mp (he ▸ isClosed_closure)).2
  exact Set.Subset.antisymm hsub (Set.insert_subset hinf subset_closure)

theorem sphericalFamily_eq {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    sphericalFamily m α = insert ∞ (((↑) : ℂ → Sphere) '' extremalCurve m α) :=
  closure_onePoint_image (extremalCurve_isClosed m α) (extremalCurve_not_isCompact hm ha)

theorem finite_mem_sphericalFamily_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (z : ℂ) :
    (z : Sphere) ∈ sphericalFamily m α ↔ z ∈ extremalCurve m α := by
  rw [sphericalFamily_eq hm ha]
  simp only [Set.mem_insert_iff, OnePoint.coe_ne_infty, false_or,
    Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right]

theorem infinity_mem_sphericalFamily {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) : (∞ : Sphere) ∈ sphericalFamily m α := by
  rw [sphericalFamily_eq hm ha]
  exact Set.mem_insert _ _

#print axioms sphereProjectiveEquiv_action
#print axioms sphericalFamily_eq
#print axioms finite_mem_sphericalFamily_iff

end CurveSymmetry
