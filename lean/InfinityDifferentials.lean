import QuadraticInfinity
import PlaceDifferentials

/-!
# Differentials at the place over `t = ∞` (G09a-2d)

G07b-3 identifies the chart at infinity of the family with the conjugate family,
through a ring isomorphism of function fields, and defines the place over
`t = ∞` as the preimage of the point place `(0, 0)` of that conjugate family.

Here that isomorphism is upgraded to an isomorphism of `ℂ`-algebras and used to
carry G09a-2b/2c to the place at infinity: the preimage of a uniformizer has a
nonzero differential that spans `Ω[K⁄ℂ]`, and coefficients read off from two
such elements differ by a unit of the local ring at infinity.

The order itself and its value on `dt` are still not defined; that is G09a-2e.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

lemma familyInfinityEquiv_coe (x : QuadField (familyH m α)) :
    familyInfinityEquiv m α x = familyInfinityMap m α x := rfl

variable (m α) in
/-- The chart isomorphism of G07b-3 as an isomorphism of `ℂ`-algebras. -/
noncomputable def familyInfinityAlgEquiv :
    QuadField (familyH m α) ≃ₐ[ℂ] QuadField (familyH m (star α)) :=
  AlgEquiv.ofRingEquiv (f := familyInfinityEquiv m α) fun r => by
    rw [familyInfinityEquiv_coe,
      IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadField (familyH m α)),
      ← Polynomial.C_eq_algebraMap, familyInfinityMap_polyC, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadField (familyH m (star α)))]

@[simp] lemma familyInfinityAlgEquiv_apply (x : QuadField (familyH m α)) :
    familyInfinityAlgEquiv m α x = familyInfinityMap m α x := rfl

/-- The conjugate family's point place `(0, 0)` is the one that the place at infinity
pulls back from. -/
lemma mem_familyInfinityPlace_iff_symm (y : quadLocalRing (familyH m (star α)) 0 0
    (familyH_star_zero_point m α)) :
    (familyInfinityAlgEquiv m α).symm (y : QuadField (familyH m (star α))) ∈
      familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace]
  show familyInfinityAlgEquiv m α ((familyInfinityAlgEquiv m α).symm _) ∈ _
  rw [AlgEquiv.apply_symm_apply]
  exact y.2

/-- **G09a-2d**: at the place over `t = ∞`, the preimage of a uniformizer of the
conjugate family's point place `(0, 0)` lies in the local ring at infinity and its
differential is a nonzero generator of `Ω[K⁄ℂ]`. -/
theorem family_infinity_differential_spans :
    ∃ x : QuadField (familyH m α),
      x ∈ familyInfinityPlace m α ∧
        (∃ u : quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α),
          IsLocalRing.maximalIdeal
              (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α)) =
            Ideal.span {u} ∧ familyInfinityMap m α x = (u : QuadField (familyH m (star α)))) ∧
        Submodule.span (QuadField (familyH m α))
            {KaehlerDifferential.D ℂ (QuadField (familyH m α)) x} = ⊤ ∧
          KaehlerDifferential.D ℂ (QuadField (familyH m α)) x ≠ 0 := by
  obtain ⟨u, hu, -⟩ :=
    quadLocal_exists_uniformizer (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
  refine ⟨(familyInfinityAlgEquiv m α).symm (u : QuadField (familyH m (star α))),
    mem_familyInfinityPlace_iff_symm u, ⟨u, hu, ?_⟩, ?_, ?_⟩
  · show familyInfinityAlgEquiv m α ((familyInfinityAlgEquiv m α).symm _) = _
    rw [AlgEquiv.apply_symm_apply]
  · exact kaehler_span_D_equiv (familyInfinityAlgEquiv m α).symm
      (quadLocal_D_uniformizer_spans (familyH m (star α)) 0 0 (familyH_star_zero_point m α) hu)
  · exact quad_D_ne_zero_of_span (familyH m α)
      (kaehler_span_D_equiv (familyInfinityAlgEquiv m α).symm
        (quadLocal_D_uniformizer_spans (familyH m (star α)) 0 0
          (familyH_star_zero_point m α) hu))

/-- Every differential of the function field is a multiple of the one above. -/
theorem family_infinity_exists_coeff {x : QuadField (familyH m α)}
    (hx : Submodule.span (QuadField (familyH m α))
      {KaehlerDifferential.D ℂ (QuadField (familyH m α)) x} = ⊤)
    (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ∃ f : QuadField (familyH m α),
      ω = f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) x := by
  have hmem : ω ∈ Submodule.span (QuadField (familyH m α))
      {KaehlerDifferential.D ℂ (QuadField (familyH m α)) x} := by rw [hx]; trivial
  obtain ⟨f, hf⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨f, hf.symm⟩

/-- Membership in the local ring at infinity is membership of the image in the conjugate
family's local ring, for an element and for its inverse. So the units used to compare two
readings of a coefficient correspond as well. -/
lemma familyInfinity_unit_iff (e : QuadField (familyH m α)) :
    (e ∈ familyInfinityPlace m α ∧ e⁻¹ ∈ familyInfinityPlace m α) ↔
      (familyInfinityMap m α e ∈
          quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α) ∧
        (familyInfinityMap m α e)⁻¹ ∈
          quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)) := by
  constructor
  · rintro ⟨he, he'⟩
    refine ⟨(mem_familyInfinityPlace e).mp he, ?_⟩
    rw [← map_inv₀ (familyInfinityMap m α)]
    exact (mem_familyInfinityPlace _).mp he'
  · rintro ⟨he, he'⟩
    refine ⟨(mem_familyInfinityPlace e).mpr he, (mem_familyInfinityPlace _).mpr ?_⟩
    rw [map_inv₀ (familyInfinityMap m α)]
    exact he'

#print axioms familyInfinityAlgEquiv
#print axioms family_infinity_differential_spans

end CurveSymmetry
