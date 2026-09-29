import FunctionFieldGenus
import HolomorphicSpan

/-!
# The family's genus at the intrinsic reading (R01b)

G09 defined the holomorphic differentials of the family's function field
through its explicit places: `IsRegularAt` at each point place `(c, d)`, and
`IsRegularAtInfinity` through the chart isomorphism. R01a defined them for any
field over `ℂ`, with places as valuation subrings. This module shows the two
agree for the family:

* at a point place, regularity in the sense of R01a is `IsRegularAt`
  (`mem_regularAt_quadPlace_iff`): the local ring's differentials are generated
  by `du` (G09a-2b), and `quadPlace` has the carrier of `quadLocalRing`;
* at the place over `t = ∞`, it is `IsRegularAtInfinity`
  (`mem_regularAt_familyInfinityPlace_iff`), since that place is the pull-back of
  the conjugate family's `(0, 0)` along the chart isomorphism;
* `family_place_classification` (G07b-3) says there are no other places.

So `holomorphicSpace` of the family's field is `holomorphicDifferentials m α`
(`family_holomorphicSpace_eq`), its genus is `m`, and through G07a's
isomorphism, made `ℂ`-linear here, so is the genus of `Frac(ℂ[X,Y]/(P_α))`
(`familyFunctionField_genus`).
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section Point

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

/-- A point place is a place over `ℂ` in the sense of R01a. -/
lemma quadPlace_isComplexPlace : IsComplexPlace (quadPlace h c d hd) :=
  ⟨((quad_finite_place_classification h).1 c d hd).1, quadLocal_const_mem h c d hd⟩

/-- **R01b, point places**: regularity at `quadPlace` in the sense of R01a is G09b-1's
`IsRegularAt`. -/
theorem mem_regularAt_quadPlace_iff (ω : Ω[QuadField h⁄ℂ]) :
    ω ∈ regularAt (quadPlace h c d hd) ↔ IsRegularAt h c d hd ω := by
  obtain ⟨u, hu, hspan⟩ := quadLocal_exists_uniformizer h c d hd
  obtain ⟨f, hf⟩ := quadLocal_exists_coeff h c d hd hu ω
  have hgen : ∀ b ∈ quadPlace h c d hd, ∃ g ∈ quadPlace h c d hd,
      KaehlerDifferential.D ℂ (QuadField h) b =
        g • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) := by
    intro b hb
    obtain ⟨g, hg⟩ := exists_D_eq_smul_of_span_eq_top (K := QuadField h) hspan ⟨b, hb⟩
    exact ⟨g, g.2, hg⟩
  rw [mem_regularAt_iff_of_generator u.2 (quadLocal_const_mem h c d hd) hgen,
    isRegularAt_iff h c d hd hu hf]
  constructor
  · rintro ⟨f', hf', hω⟩
    have hdu := quadLocal_D_uniformizer_ne_zero h c d hd hu
    have hsub : (f - f') • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) = 0 := by
      rw [sub_smul, ← hf, ← hω, sub_self]
    rcases smul_eq_zero.mp hsub with h0 | h0
    · rw [sub_eq_zero.mp h0]
      exact hf'
    · exact absurd h0 hdu
  · intro hfmem
    exact ⟨f, hfmem, hf⟩

end Point

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- The place over `t = ∞` is the pull-back of the conjugate family's `(0, 0)` along the
chart isomorphism of `ℂ`-algebras. -/
lemma familyInfinityPlace_eq_comap :
    familyInfinityPlace m α =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).comap
        (familyInfinityAlgEquiv m α :
          QuadField (familyH m α) →+* QuadField (familyH m (star α))) := by
  ext x
  rfl

lemma familyInfinityPlace_isComplexPlace : IsComplexPlace (familyInfinityPlace m α) := by
  rw [familyInfinityPlace_eq_comap]
  exact (quadPlace_isComplexPlace _ 0 0 _).comap _

/-- **R01b, infinity**: regularity at the place over `t = ∞` in the sense of R01a is
G09b-2's `IsRegularAtInfinity`. -/
theorem mem_regularAt_familyInfinityPlace_iff (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ω ∈ regularAt (familyInfinityPlace m α) ↔ IsRegularAtInfinity ω := by
  rw [familyInfinityPlace_eq_comap, mem_regularAt_comap_iff, mem_regularAt_quadPlace_iff]
  rfl

/-- Every place of the family's function field is a point place or the place at
infinity (`family_place_classification`, with the constants stated through `ℂ`). -/
lemma IsComplexPlace.family_cases {O : ValuationSubring (QuadField (familyH m α))}
    (hO : IsComplexPlace O) :
    (∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∨
      O = familyInfinityPlace m α := by
  refine (family_place_classification (m := m) (α := α)).2 O hO.1 fun c => ?_
  rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  exact hO.2 c

/-- **R01b**: for the family, the holomorphic differentials of R01a are those of G09. -/
theorem family_holomorphicSpace_eq :
    holomorphicSpace (QuadField (familyH m α)) = holomorphicDifferentials m α := by
  ext ω
  rw [mem_holomorphicSpace, mem_holomorphicDifferentials, IsHolomorphic]
  constructor
  · intro hω
    exact ⟨fun c d hd => (mem_regularAt_quadPlace_iff _ c d hd ω).mp
        (hω _ (quadPlace_isComplexPlace _ c d hd)),
      (mem_regularAt_familyInfinityPlace_iff ω).mp (hω _ familyInfinityPlace_isComplexPlace)⟩
  · rintro ⟨hpts, hinf⟩ O hO
    rcases hO.family_cases with ⟨c, d, hd, rfl⟩ | rfl
    · exact (mem_regularAt_quadPlace_iff _ c d hd ω).mpr (hpts c d hd)
    · exact (mem_regularAt_familyInfinityPlace_iff ω).mpr hinf

/-- The genus of the double cover's function field is `m`. -/
theorem genus_quadField_family : genus (QuadField (familyH m α)) = m := by
  rw [genus, family_holomorphicSpace_eq, family_genus]

variable (m α) in
/-- G07a's comparison map `ℂ(t)[w]/(w² − h) → Frac(ℂ[X,Y]/(P_α))`, typed on `QuadField`. -/
noncomputable def familyQuadLift : QuadField (familyH m α) →+* FamilyFunctionField m α :=
  familyLift m α

lemma familyQuadLift_bijective : Function.Bijective (familyQuadLift m α) :=
  ⟨familyLift_injective, familyLift_surjective⟩

variable (m α) in
/-- G07a's isomorphism `ℂ(t)[w]/(w² − h) ≅ Frac(ℂ[X,Y]/(P_α))`, as `ℂ`-algebras. -/
noncomputable def familyFunctionFieldAlgEquiv :
    QuadField (familyH m α) ≃ₐ[ℂ] FamilyFunctionField m α :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective (familyQuadLift m α) familyQuadLift_bijective)
    fun z => by
      rw [RingEquiv.ofBijective_apply,
        IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (QuadField (familyH m α)),
        AdjoinRoot.algebraMap_eq]
      exact (familyLift_of _).trans ((familyRatFuncHom m α).commutes z)

@[simp] lemma familyFunctionFieldAlgEquiv_apply (x : QuadField (familyH m α)) :
    familyFunctionFieldAlgEquiv m α x = familyQuadLift m α x :=
  rfl

/-- **R01b**: the function field of the family curve, `Frac(ℂ[X,Y]/(P_α))`, has genus `m` in
the sense of R01a. -/
theorem familyFunctionField_genus : genus (FamilyFunctionField m α) = m :=
  (genus_congr (familyFunctionFieldAlgEquiv m α)).symm.trans genus_quadField_family

#print axioms mem_regularAt_quadPlace_iff
#print axioms mem_regularAt_familyInfinityPlace_iff
#print axioms family_holomorphicSpace_eq
#print axioms familyFunctionField_genus

end CurveSymmetry
