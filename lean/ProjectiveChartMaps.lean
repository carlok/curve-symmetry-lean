import FamilyProjective

namespace CurveSymmetry

noncomputable section
open OnePoint

set_option autoImplicit false

/-- Standard projective-line charts `[z:1]` and `[1:z]`. These definitions
make no topological assertion. -/
def affineLinePoint (z : ℂ) : ProjectiveLine :=
  Projectivization.mk ℂ ![z, 1] (by simp)

def reciprocalLinePoint (z : ℂ) : ProjectiveLine :=
  Projectivization.mk ℂ ![1, z] (by simp)

theorem reciprocalLinePoint_overlap {z : ℂ} (hz : z ≠ 0) :
    reciprocalLinePoint z = affineLinePoint z⁻¹ := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  refine ⟨z, ?_⟩
  ext i
  fin_cases i <;> simp [hz]

def affineProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (affineLinePoint (w 0), affineLinePoint (w 1))

def mixedProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (reciprocalLinePoint (w 0), affineLinePoint (w 1))

/-- The second mixed chart uses the order `(1/Y,X)`, as in the closure proof. -/
def otherMixedProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (affineLinePoint (w 1), reciprocalLinePoint (w 0))

def reciprocalProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (reciprocalLinePoint (w 0), reciprocalLinePoint (w 1))

theorem mixedProjectiveChart_overlap (w : Fin 2 → ℂ) (h0 : w 0 ≠ 0) :
    mixedProjectiveChart w = affineProjectiveChart ![(w 0)⁻¹, w 1] := by
  simp [mixedProjectiveChart, affineProjectiveChart, reciprocalLinePoint_overlap h0]

theorem otherMixedProjectiveChart_overlap (w : Fin 2 → ℂ) (h0 : w 0 ≠ 0) :
    otherMixedProjectiveChart w = affineProjectiveChart ![w 1, (w 0)⁻¹] := by
  simp [otherMixedProjectiveChart, affineProjectiveChart, reciprocalLinePoint_overlap h0]

theorem reciprocalProjectiveChart_overlap (w : Fin 2 → ℂ)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    reciprocalProjectiveChart w = affineProjectiveChart ![(w 0)⁻¹, (w 1)⁻¹] := by
  simp [reciprocalProjectiveChart, affineProjectiveChart,
    reciprocalLinePoint_overlap h0, reciprocalLinePoint_overlap h1]

theorem affineProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    affineProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyPolynomial m α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_affine])

theorem mixedProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    mixedProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyMixedPolynomial m α (star α)) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_mixed])

theorem otherMixedProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    otherMixedProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyMixedPolynomial m (star α) α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_other_mixed])

theorem reciprocalProjectiveChart_mem (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) :
    reciprocalProjectiveChart w ∈ familyProjectiveCurve m α ↔
      planeEval (w 0) (w 1) (familyInfinityPolynomial m α) = 0 := by
  exact (familyProjective_mk_iff m α _ _ _ _).trans
    (by rw [familyBihomogeneous_reciprocal])

/-- The chart origins are precisely the three previously classified boundary
points. This is an identity of points, not a closure or gluing theorem. -/
theorem projectiveChart_origins :
    mixedProjectiveChart ![0, 0] =
      (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv ((0 : ℂ) : Sphere)) ∧
    otherMixedProjectiveChart ![0, 0] =
      (sphereProjectiveEquiv ((0 : ℂ) : Sphere), sphereProjectiveEquiv (∞ : Sphere)) ∧
    reciprocalProjectiveChart ![0, 0] =
      (sphereProjectiveEquiv (∞ : Sphere), sphereProjectiveEquiv (∞ : Sphere)) := by
  exact ⟨rfl, rfl, rfl⟩

theorem affineLinePoint_injective : Function.Injective affineLinePoint := by
  intro x y h
  change sphereProjectiveEquiv (x : Sphere) = sphereProjectiveEquiv (y : Sphere) at h
  exact OnePoint.coe_injective (sphereProjectiveEquiv.injective h)

theorem reciprocalLinePoint_injective : Function.Injective reciprocalLinePoint := by
  intro x y h
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h0
  simpa [h0] using h1.symm

theorem affineProjectiveChart_injective : Function.Injective affineProjectiveChart := by
  intro v w h
  have h0 := affineLinePoint_injective (congrArg Prod.fst h)
  have h1 := affineLinePoint_injective (congrArg Prod.snd h)
  ext i
  fin_cases i <;> assumption

theorem mixedProjectiveChart_injective : Function.Injective mixedProjectiveChart := by
  intro v w h
  have h0 := reciprocalLinePoint_injective (congrArg Prod.fst h)
  have h1 := affineLinePoint_injective (congrArg Prod.snd h)
  ext i
  fin_cases i <;> assumption

theorem otherMixedProjectiveChart_injective : Function.Injective otherMixedProjectiveChart := by
  intro v w h
  have h1 := affineLinePoint_injective (congrArg Prod.fst h)
  have h0 := reciprocalLinePoint_injective (congrArg Prod.snd h)
  ext i
  fin_cases i <;> assumption

theorem reciprocalProjectiveChart_injective : Function.Injective reciprocalProjectiveChart := by
  intro v w h
  have h0 := reciprocalLinePoint_injective (congrArg Prod.fst h)
  have h1 := reciprocalLinePoint_injective (congrArg Prod.snd h)
  ext i
  fin_cases i <;> assumption

theorem projectiveLine_chart_cover (p : ProjectiveLine) :
    (∃ z, affineLinePoint z = p) ∨ (∃ z, reciprocalLinePoint z = p) := by
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  cases u using OnePoint.rec with
  | infty => exact Or.inr ⟨0, rfl⟩
  | coe z => exact Or.inl ⟨z, rfl⟩

/-- Every projective pair has coordinates in one of these four injective
charts. This set-theoretic cover does not assert open embeddings. -/
theorem projectiveChart_cover (p : ProjectiveLine × ProjectiveLine) :
    (∃ w, affineProjectiveChart w = p) ∨
    (∃ w, mixedProjectiveChart w = p) ∨
    (∃ w, otherMixedProjectiveChart w = p) ∨
    (∃ w, reciprocalProjectiveChart w = p) := by
  rcases p with ⟨p, q⟩
  rcases projectiveLine_chart_cover p with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    rcases projectiveLine_chart_cover q with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact Or.inl ⟨![x, y], rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨![y, x], rfl⟩))
  · exact Or.inr (Or.inl ⟨![x, y], rfl⟩)
  · exact Or.inr (Or.inr (Or.inr ⟨![x, y], rfl⟩))

/-- The finite chart omits exactly infinity. -/
theorem affineLinePoint_range (p : ProjectiveLine) :
    p ∈ Set.range affineLinePoint ↔ p ≠ sphereProjectiveEquiv (∞ : Sphere) := by
  obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
  cases u using OnePoint.rec with
  | infty =>
      constructor
      · rintro ⟨z, hz⟩
        change sphereProjectiveEquiv (z : Sphere) = sphereProjectiveEquiv ∞ at hz
        exact (OnePoint.coe_ne_infty z (sphereProjectiveEquiv.injective hz)).elim
      · intro h; exact (h rfl).elim
  | coe z =>
      constructor
      · intro _ h
        exact OnePoint.coe_ne_infty z (sphereProjectiveEquiv.injective h)
      · intro _; exact ⟨z, rfl⟩

/-- The reciprocal chart omits exactly the finite point zero. -/
theorem reciprocalLinePoint_range (p : ProjectiveLine) :
    p ∈ Set.range reciprocalLinePoint ↔ p ≠ affineLinePoint 0 := by
  constructor
  · rintro ⟨z, rfl⟩ h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h
    have h0 := congrFun ha 0
    simp at h0
  · intro hp
    obtain ⟨u, rfl⟩ := sphereProjectiveEquiv.surjective p
    cases u using OnePoint.rec with
    | infty => exact ⟨0, rfl⟩
    | coe z =>
        have hz : z ≠ 0 := by intro h; subst z; exact hp rfl
        refine ⟨z⁻¹, ?_⟩
        rw [reciprocalLinePoint_overlap (inv_ne_zero hz), inv_inv]
        rfl

private lemma pair_chart_range (f g : ℂ → ProjectiveLine)
    (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range (fun w : Fin 2 → ℂ => (f (w 0), g (w 1))) ↔
      p.1 ∈ Set.range f ∧ p.2 ∈ Set.range g := by
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨⟨w 0, rfl⟩, ⟨w 1, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨![x, y], Prod.ext hx hy⟩

theorem affineProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range affineProjectiveChart ↔
      p.1 ≠ sphereProjectiveEquiv (∞ : Sphere) ∧
      p.2 ≠ sphereProjectiveEquiv (∞ : Sphere) := by
  unfold affineProjectiveChart
  rw [pair_chart_range, affineLinePoint_range, affineLinePoint_range]

theorem mixedProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range mixedProjectiveChart ↔
      p.1 ≠ affineLinePoint 0 ∧ p.2 ≠ sphereProjectiveEquiv (∞ : Sphere) := by
  unfold mixedProjectiveChart
  rw [pair_chart_range, reciprocalLinePoint_range, affineLinePoint_range]

theorem otherMixedProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range otherMixedProjectiveChart ↔
      p.1 ≠ sphereProjectiveEquiv (∞ : Sphere) ∧ p.2 ≠ affineLinePoint 0 := by
  rw [← affineLinePoint_range, ← reciprocalLinePoint_range]
  constructor
  · rintro ⟨w, rfl⟩; exact ⟨⟨w 1, rfl⟩, ⟨w 0, rfl⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨![y, x], Prod.ext hx hy⟩

theorem reciprocalProjectiveChart_range (p : ProjectiveLine × ProjectiveLine) :
    p ∈ Set.range reciprocalProjectiveChart ↔
      p.1 ≠ affineLinePoint 0 ∧ p.2 ≠ affineLinePoint 0 := by
  unfold reciprocalProjectiveChart
  rw [pair_chart_range,
    reciprocalLinePoint_range, reciprocalLinePoint_range]

#print axioms reciprocalProjectiveChart_range
#print axioms otherMixedProjectiveChart_range
#print axioms projectiveChart_cover
#print axioms reciprocalProjectiveChart_injective
#print axioms reciprocalProjectiveChart_overlap
#print axioms projectiveChart_origins

end
end CurveSymmetry
