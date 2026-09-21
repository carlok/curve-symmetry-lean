import FamilyAmbientGroup
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace CurveSymmetry
set_option autoImplicit false
open OnePoint
noncomputable section

theorem sphereDilationPerm_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereDilationPerm a ha * sphereDilationPerm b hb =
      sphereDilationPerm (a * b) (mul_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec <;>
    simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereDilation, mul_assoc]

theorem sphereDilationPerm_mul_inversion (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereDilationPerm a ha * sphereInversionPerm b hb =
      sphereInversionPerm (a * b) (mul_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply,
      sphereInversionPerm_apply, sphereDilation, sphereInversion]
  | coe z =>
    by_cases hz : z = 0 <;>
      simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereInversionPerm_apply,
        sphereDilation, sphereInversion, hz, mul_div_assoc]

theorem sphereInversionPerm_mul_dilation (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereInversionPerm a ha * sphereDilationPerm b hb =
      sphereInversionPerm (a / b) (div_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply,
      sphereInversionPerm_apply, sphereDilation, sphereInversion]
  | coe z =>
    by_cases hz : z = 0 <;>
      simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereInversionPerm_apply,
        sphereDilation, sphereInversion, hz, hb, div_mul_eq_div_div]

theorem sphereInversionPerm_mul (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    sphereInversionPerm a ha * sphereInversionPerm b hb =
      sphereDilationPerm (a / b) (div_ne_zero ha hb) := by
  ext p
  cases p using OnePoint.rec with
  | infty => simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply,
      sphereInversionPerm_apply, sphereDilation, sphereInversion]
  | coe z =>
    by_cases hz : z = 0 <;>
      simp [Equiv.Perm.mul_apply, sphereDilationPerm_apply, sphereInversionPerm_apply,
        sphereDilation, sphereInversion, hz, hb, div_div_eq_mul_div, div_mul_eq_mul_div]

/-- A cyclic parametrization of all complex nth roots. -/
def complexRootEquiv (n : ℕ) [NeZero n] :
    Multiplicative (ZMod n) ≃* rootsOfUnity n ℂ :=
  mulEquivOfCyclicCardEq (by rw [Complex.card_rootsOfUnity]; simp)

def rootCharacter (n : ℕ) [NeZero n] (i : ZMod n) : ℂ :=
  ((complexRootEquiv n (Multiplicative.ofAdd i)).val : ℂ)

theorem rootCharacter_ne_zero (n : ℕ) [NeZero n] (i : ZMod n) :
    rootCharacter n i ≠ 0 := Units.ne_zero _

theorem rootCharacter_pow (n : ℕ) [NeZero n] (i : ZMod n) :
    rootCharacter n i ^ n = 1 :=
  (mem_rootsOfUnity' _ _).mp (complexRootEquiv n (Multiplicative.ofAdd i)).property

theorem rootCharacter_add (n : ℕ) [NeZero n] (i j : ZMod n) :
    rootCharacter n (i + j) = rootCharacter n i * rootCharacter n j := by
  exact congrArg (fun u : rootsOfUnity n ℂ => (u.val : ℂ))
    ((complexRootEquiv n).map_mul (Multiplicative.ofAdd i) (Multiplicative.ofAdd j))

theorem rootCharacter_sub (n : ℕ) [NeZero n] (i j : ZMod n) :
    rootCharacter n (i - j) = rootCharacter n i / rootCharacter n j := by
  simp [rootCharacter]

theorem rootCharacter_injective (n : ℕ) [NeZero n] :
    Function.Injective (rootCharacter n) := by
  intro i j h
  have he : complexRootEquiv n (Multiplicative.ofAdd i) =
      complexRootEquiv n (Multiplicative.ofAdd j) := rootsOfUnity.coe_injective h
  exact (complexRootEquiv n).injective he

theorem rootCharacter_surjective (n : ℕ) [NeZero n] {c : ℂ} (hc : c ^ n = 1) :
    ∃ i : ZMod n, rootCharacter n i = c := by
  obtain ⟨i, hi⟩ := (complexRootEquiv n).surjective (rootsOfUnity.mkOfPowEq c hc)
  exact ⟨Multiplicative.toAdd i, congrArg (fun u : rootsOfUnity n ℂ => (u.val : ℂ)) hi⟩

/-- The standard dihedral action: r(i) is multiplication by the ith root,
and sr(i) is inversion with coefficient b divided by that root. -/
def dihedralSphereMap (n : ℕ) [NeZero n] (b : ℂ) (hb : b ≠ 0) :
    DihedralGroup n → Equiv.Perm Sphere
  | .r i => sphereDilationPerm (rootCharacter n i) (rootCharacter_ne_zero n i)
  | .sr i => sphereInversionPerm (b / rootCharacter n i)
      (div_ne_zero hb (rootCharacter_ne_zero n i))

theorem dihedralSphereMap_mul (n : ℕ) [NeZero n] (b : ℂ) (hb : b ≠ 0)
    (x y : DihedralGroup n) :
    dihedralSphereMap n b hb (x * y) =
      dihedralSphereMap n b hb x * dihedralSphereMap n b hb y := by
  cases x with
  | r i =>
    cases y with
    | r j => simp [dihedralSphereMap, sphereDilationPerm_mul, rootCharacter_add]
    | sr j =>
      simp only [DihedralGroup.r_mul_sr, dihedralSphereMap,
        sphereDilationPerm_mul_inversion]
      congr 1
      rw [rootCharacter_sub]
      field_simp
  | sr i =>
    cases y with
    | r j =>
      simp only [DihedralGroup.sr_mul_r, dihedralSphereMap,
        sphereInversionPerm_mul_dilation]
      congr 1
      rw [rootCharacter_add]
      field_simp
    | sr j =>
      simp only [DihedralGroup.sr_mul_sr, dihedralSphereMap, sphereInversionPerm_mul]
      congr 1
      rw [rootCharacter_sub]
      field_simp

theorem dihedralSphereMap_injective (n : ℕ) [NeZero n] (b : ℂ) (hb : b ≠ 0) :
    Function.Injective (dihedralSphereMap n b hb) := by
  intro x y h
  cases x with
  | r i =>
    cases y with
    | r j =>
      exact congrArg DihedralGroup.r (rootCharacter_injective n
        (sphereDilationPerm_injective _ _ h))
    | sr j => exact False.elim (sphereDilationPerm_ne_inversion _ _ _ _ h)
  | sr i =>
    cases y with
    | r j => exact False.elim (sphereDilationPerm_ne_inversion _ _ _ _ h.symm)
    | sr j =>
      have he := sphereInversionPerm_injective _ _ h
      have hr : rootCharacter n i = rootCharacter n j := by
        have hi := rootCharacter_ne_zero n i
        have hj := rootCharacter_ne_zero n j
        field_simp at he
        exact he.symm
      exact congrArg DihedralGroup.sr (rootCharacter_injective n hr)

theorem dihedralSphereMap_mem {m : ℕ} [NeZero (2 * m)] (hm : 0 < m) {α b : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hb : b ≠ 0) (hbr : b ^ (2 * m) = star α ^ 2)
    (x : DihedralGroup (2 * m)) :
    dihedralSphereMap (2 * m) b hb x ∈ familyAmbientGroup m α := by
  cases x with
  | r i => exact sphereDilationPerm_mem hm ha hα _ (rootCharacter_pow _ i)
  | sr i =>
    apply sphereInversionPerm_mem hm ha hα
    simp [div_pow, rootCharacter_pow, hbr]

theorem dihedralSphereMap_surjective {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    {α b : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (hb : b ≠ 0)
    (hbr : b ^ (2 * m) = star α ^ 2) (f : familyAmbientGroup m α) :
    ∃ x : DihedralGroup (2 * m), dihedralSphereMap (2 * m) b hb x = f.val := by
  obtain ⟨c, hc, ⟨hr, he⟩ | ⟨hr, he⟩⟩ := familyAmbientGroup_normal_forms hm ha hα f
  · obtain ⟨i, hi⟩ := rootCharacter_surjective (2 * m) hr
    refine ⟨.r i, ?_⟩
    simp [dihedralSphereMap, ← he, hi]
  · have hbc : (b / c) ^ (2 * m) = 1 := by
      rw [div_pow, hbr, ← hr]
      exact div_self (pow_ne_zero _ hc)
    obtain ⟨i, hi⟩ := rootCharacter_surjective (2 * m) hbc
    refine ⟨.sr i, ?_⟩
    have hi' : b / rootCharacter (2 * m) i = c := by rw [hi]; field_simp
    simp [dihedralSphereMap, hi', he]

/-- Explicit dihedral isomorphism once a base inversion coefficient is chosen. -/
def familyDihedralEquivOfRoot {m : ℕ} [NeZero (2 * m)] (hm : 2 ≤ m)
    {α b : ℂ} (ha : α ≠ star α) (hα : ‖α‖ = 1) (hb : b ≠ 0)
    (hbr : b ^ (2 * m) = star α ^ 2) :
    DihedralGroup (2 * m) ≃* familyAmbientGroup m α :=
  MulEquiv.ofBijective
    ({ toFun := fun x => ⟨dihedralSphereMap (2 * m) b hb x,
          dihedralSphereMap_mem (by omega) ha hα hb hbr x⟩
       map_one' := by
         apply Subtype.ext
         ext p
         change sphereDilationPerm (rootCharacter (2 * m) 0) _ p = p
         cases p using OnePoint.rec <;>
           simp [rootCharacter, sphereDilationPerm_apply, sphereDilation]
       map_mul' := by
         intro x y
         exact Subtype.ext (dihedralSphereMap_mul _ b hb x y) } :
       DihedralGroup (2 * m) →* familyAmbientGroup m α)
    ⟨fun _ _ h => dihedralSphereMap_injective _ b hb (congrArg Subtype.val h),
      fun f => by
        obtain ⟨x, hx⟩ := dihedralSphereMap_surjective hm ha hα hb hbr f
        exact ⟨x, Subtype.ext hx⟩⟩

/-- The full group of actual ambient Möbius symmetries is dihedral.
The earlier no-anti-map theorem excludes anti-Möbius additions. -/
theorem familyAmbientGroup_dihedral {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nonempty (DihedralGroup (2 * m) ≃* familyAmbientGroup m α) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (star α ^ 2) (by omega : 0 < 2 * m)
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  have hb0 : b ≠ 0 := by
    intro h
    have hz : star α ^ 2 = 0 := by simpa [h, Nat.ne_of_gt (by omega : 0 < 2 * m)] using hb.symm
    exact (pow_ne_zero 2 (star_ne_zero.mpr ha0)) hz
  exact ⟨familyDihedralEquivOfRoot hm ha hα hb0 hb⟩

theorem familyAmbientGroup_card {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    Nat.card (familyAmbientGroup m α) = 4 * m := by
  obtain ⟨e⟩ := familyAmbientGroup_dihedral hm ha hα
  rw [← Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  omega

/-- Generators, exact rotation order, involution, conjugation relation, and
exhaustion by the two usual normal forms. This includes m = 2. -/
theorem familyAmbientGroup_generators {m : ℕ} (hm : 2 ≤ m) {α : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) :
    ∃ r s : familyAmbientGroup m α,
      orderOf r = 2 * m ∧ orderOf s = 2 ∧ s * r * s = r⁻¹ ∧
      ∀ g, ∃ i : ℕ, i < 2 * m ∧ (g = r ^ i ∨ g = s * r ^ i) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨e⟩ := familyAmbientGroup_dihedral hm ha hα
  refine ⟨e (.r 1), e (.sr 0), ?_, ?_, ?_, ?_⟩
  · rw [e.orderOf_eq, DihedralGroup.orderOf_r_one]
  · rw [e.orderOf_eq, DihedralGroup.orderOf_sr]
  · rw [← map_mul, ← map_mul, ← map_inv]
    congr 1
    simp
  · intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    cases x with
    | r i =>
      refine ⟨i.val, ZMod.val_lt i, Or.inl ?_⟩
      rw [← map_pow]
      congr 1
      simp
    | sr i =>
      refine ⟨i.val, ZMod.val_lt i, Or.inr ?_⟩
      rw [← map_pow, ← map_mul]
      congr 1
      simp

#print axioms familyAmbientGroup_dihedral
#print axioms familyAmbientGroup_card
#print axioms familyAmbientGroup_generators

end
end CurveSymmetry
