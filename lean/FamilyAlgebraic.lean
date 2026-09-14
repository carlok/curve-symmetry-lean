import FamilyAmbientGroup
import Mathlib.RingTheory.Algebraic.Integral

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section

/-- The root conditions imply algebraicity over Q, not just over C. -/
theorem family_root_coefficient_algebraic {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : IsAlgebraic ℚ α)
    (hc : c ^ (2 * m) = 1 ∨ c ^ (2 * m) = star α ^ 2) :
    IsAlgebraic ℚ c := by
  apply IsAlgebraic.of_pow (by omega : 0 < 2 * m)
  rcases hc with hc | hc
  · rw [hc]
    exact isAlgebraic_one
  · rw [hc]
    have hs : IsIntegral ℚ (star α) :=
      hα.isIntegral.map (Complex.conjAe.restrictScalars ℚ).toAlgHom
    exact (hs.pow 2).isAlgebraic

/-- Every ambient self-map has an algebraic normal-form coefficient when
the normalized family parameter is algebraic. -/
theorem family_mobius_algebraic_forms {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (g : MobiusMatrix)
    (hg : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) :
    ∃ c : ℂ, c ≠ 0 ∧ IsAlgebraic ℚ c ∧
      ((c ^ (2 * m) = 1 ∧ ∀ p : Sphere, g • p = sphereDilation c p) ∨
       (c ^ (2 * m) = star α ^ 2 ∧ ∀ p : Sphere, g • p = sphereInversion c p)) := by
  obtain ⟨c, hc, h⟩ := (family_mobius_self_filter hm ha hα g).mp hg
  refine ⟨c, hc, family_root_coefficient_algebraic (m := m) (by omega) halg ?_, h⟩
  exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)

/-- Algebraic coefficients means existence of a GL(2,C) representative with
algebraic entries. An arbitrary scalar rescaling need not have that property. -/
theorem family_mobius_algebraic_representative {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (g : MobiusMatrix)
    (hg : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α) :
    ∃ h : MobiusMatrix, (∀ i j, IsAlgebraic ℚ (h i j)) ∧
      ∀ p : Sphere, h • p = g • p := by
  obtain ⟨c, hc, hca, ⟨hr, he⟩ | ⟨hr, he⟩⟩ :=
    family_mobius_algebraic_forms hm ha hα halg g hg
  · let h : MobiusMatrix := Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1]
      (by simpa [Matrix.det_fin_two] using hc)
    refine ⟨h, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        first | exact hca | exact isAlgebraic_zero | exact isAlgebraic_one
    · intro p
      rw [he]
      simpa [h, Matrix.GeneralLinearGroup.mkOfDetNeZero] using
        (mobius_diagonal_action h rfl rfl).2 p
  · let h : MobiusMatrix := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, c; 1, 0]
      (by simpa [Matrix.det_fin_two] using hc)
    refine ⟨h, ?_, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j <;>
        first | exact hca | exact isAlgebraic_zero | exact isAlgebraic_one
    · intro p
      rw [he]
      simpa [h, Matrix.GeneralLinearGroup.mkOfDetNeZero] using
        (mobius_antidiagonal_action h rfl rfl).2 p

/-- Representative statement directly on the actual transformation group. -/
theorem familyAmbientGroup_algebraic_representative {m : ℕ} (hm : 2 ≤ m)
    {α : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (halg : IsAlgebraic ℚ α)
    (f : familyAmbientGroup m α) :
    ∃ h : MobiusMatrix, (∀ i j, IsAlgebraic ℚ (h i j)) ∧
      ∀ p : Sphere, h • p = f.val p := by
  obtain ⟨⟨g, hg⟩, hf⟩ := (mem_familyAmbientGroup_iff m α f.val).mp f.property
  obtain ⟨h, hh, he⟩ := family_mobius_algebraic_representative hm ha hα halg g
    (fun p hp => by rw [hg]; exact (hf p).mpr hp)
  exact ⟨h, hh, fun p => (he p).trans (hg p)⟩

#print axioms familyAmbientGroup_algebraic_representative
#print axioms family_mobius_algebraic_forms
#print axioms family_mobius_algebraic_representative
end
end CurveSymmetry
