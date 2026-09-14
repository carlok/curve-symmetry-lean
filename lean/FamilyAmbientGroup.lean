import FamilySphereClassification

namespace CurveSymmetry

set_option autoImplicit false
open OnePoint
noncomputable section

/-- Permutations preserving a set in both directions. -/
def sphereSetStabilizer (S : Set Sphere) : Subgroup (Equiv.Perm Sphere) where
  carrier := {f | ∀ p, f p ∈ S ↔ p ∈ S}
  one_mem' := by intro p; rfl
  mul_mem' := by
    intro f g hf hg p
    exact (hf (g p)).trans (hg p)
  inv_mem' := by
    intro f hf p
    simpa using (hf (f⁻¹ p)).symm

/-- The full image of GL(2,C) in actual sphere permutations. Scalar-equivalent
matrices therefore represent the same element, not extra group elements. -/
def sphereMobiusHom : MobiusMatrix →* Equiv.Perm Sphere :=
  MulAction.toPermHom MobiusMatrix Sphere

/-- Actual ambient Möbius symmetries, independently of the anticipated normal
forms or root conditions. The no-anti-map theorem excludes the other parity. -/
def familyAmbientGroup (m : ℕ) (α : ℂ) : Subgroup (Equiv.Perm Sphere) :=
  sphereMobiusHom.range ⊓ sphereSetStabilizer (sphericalFamily m α)

theorem mem_familyAmbientGroup_iff (m : ℕ) (α : ℂ) (f : Equiv.Perm Sphere) :
    f ∈ familyAmbientGroup m α ↔
      (∃ g : MobiusMatrix, ∀ p : Sphere, g • p = f p) ∧
        ∀ p, f p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  constructor
  · rintro ⟨⟨g, hg⟩, hf⟩
    exact ⟨⟨g, fun p => congrArg (fun k : Equiv.Perm Sphere => k p) hg⟩, hf⟩
  · rintro ⟨⟨g, hg⟩, hf⟩
    exact ⟨⟨g, Equiv.ext hg⟩, hf⟩

private def dilationMatrix (c : ℂ) (hc : c ≠ 0) : MobiusMatrix :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1]
    (by simpa [Matrix.det_fin_two] using hc)

private def inversionMatrix (c : ℂ) (hc : c ≠ 0) : MobiusMatrix :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, c; 1, 0]
    (by simpa [Matrix.det_fin_two] using hc)

def sphereDilationPerm (c : ℂ) (hc : c ≠ 0) : Equiv.Perm Sphere :=
  sphereMobiusHom (dilationMatrix c hc)

def sphereInversionPerm (c : ℂ) (hc : c ≠ 0) : Equiv.Perm Sphere :=
  sphereMobiusHom (inversionMatrix c hc)

theorem sphereDilationPerm_apply (c : ℂ) (hc : c ≠ 0) (p : Sphere) :
    sphereDilationPerm c hc p = sphereDilation c p := by
  exact (mobius_diagonal_action (dilationMatrix c hc) rfl rfl).2 p |>.trans
    (by simp [dilationMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero])

theorem sphereInversionPerm_apply (c : ℂ) (hc : c ≠ 0) (p : Sphere) :
    sphereInversionPerm c hc p = sphereInversion c p := by
  exact (mobius_antidiagonal_action (inversionMatrix c hc) rfl rfl).2 p |>.trans
    (by simp [inversionMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero])

theorem sphereDilationPerm_mem {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0) (hr : c ^ (2 * m) = 1) :
    sphereDilationPerm c hc ∈ familyAmbientGroup m α := by
  refine ⟨⟨dilationMatrix c hc, rfl⟩, ?_⟩
  intro p
  rw [sphereDilationPerm_apply]
  exact family_sphere_dilation_mem_iff hm ha hα hc hr p

theorem sphereInversionPerm_mem {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0)
    (hr : c ^ (2 * m) = star α ^ 2) :
    sphereInversionPerm c hc ∈ familyAmbientGroup m α := by
  refine ⟨⟨inversionMatrix c hc, rfl⟩, ?_⟩
  intro p
  rw [sphereInversionPerm_apply]
  exact family_sphere_inversion_mem_iff hm hα ha hc hr p

/-- The previously proved ambient completeness theorem now classifies the
elements of the independently defined actual transformation group. -/
theorem familyAmbientGroup_normal_forms {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (f : familyAmbientGroup m α) :
    ∃ c : ℂ, ∃ hc : c ≠ 0,
      (c ^ (2 * m) = 1 ∧ f.val = sphereDilationPerm c hc) ∨
      (c ^ (2 * m) = star α ^ 2 ∧ f.val = sphereInversionPerm c hc) := by
  obtain ⟨⟨g, hg⟩, hf⟩ := (mem_familyAmbientGroup_iff m α f.val).mp f.property
  have hi : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m α := by
    intro p hp
    rw [hg]
    exact (hf p).mpr hp
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ := (family_mobius_self_filter hm ha hα g).mp hi
  · refine ⟨c, hc, Or.inl ⟨hr, ?_⟩⟩
    ext p
    rw [sphereDilationPerm_apply, ← hg, he]
  · refine ⟨c, hc, Or.inr ⟨hr, ?_⟩⟩
    ext p
    rw [sphereInversionPerm_apply, ← hg, he]

theorem sphereDilationPerm_injective {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : sphereDilationPerm a ha = sphereDilationPerm b hb) : a = b := by
  have he := congrArg (fun f : Equiv.Perm Sphere => f ((1 : ℂ) : Sphere)) h
  simpa [sphereDilationPerm_apply, sphereDilation] using he

theorem sphereInversionPerm_injective {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : sphereInversionPerm a ha = sphereInversionPerm b hb) : a = b := by
  have he := congrArg (fun f : Equiv.Perm Sphere => f ((1 : ℂ) : Sphere)) h
  simpa [sphereInversionPerm_apply, sphereInversion] using he

theorem sphereDilationPerm_ne_inversion (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereDilationPerm a ha ≠ sphereInversionPerm b hb := by
  intro h
  have he := congrArg (fun f : Equiv.Perm Sphere => f ((0 : ℂ) : Sphere)) h
  simp [sphereDilationPerm_apply, sphereInversionPerm_apply, sphereDilation, sphereInversion]
    at he

#print axioms familyAmbientGroup_normal_forms
#print axioms sphereDilationPerm_ne_inversion

end
end CurveSymmetry
