import QuadraticInfinity
import PlaceDifferentials
import PlaceUniformizers

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

/-! ### The order of `dt` at infinity (G09a-2g) -/

/-- The chart isomorphism sends `t` to `1/s`. -/
lemma familyInfinityAlgEquiv_quadT :
    familyInfinityAlgEquiv m α (quadT (familyH m α)) =
      (quadT (familyH m (star α)))⁻¹ := by
  rw [familyInfinityAlgEquiv_apply, quadT, familyInfinityMap_t, quadT]

lemma quadT_ne_zero (h : ℂ[X]) [Fact (Irreducible (quadRat h))] : quadT h ≠ 0 := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
    (RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero)

/-- **G09a-2g**: read through the chart isomorphism, `dt` at the place over `t = ∞` becomes
`−2w'·dw'` divided by `s²·h_conj'(s)`. The conjugate place `(0, 0)` is ramified, so `w'` is
its uniformizer and `s` is `w'²` times a unit (G09a-2f); `h_conj'(s)` is a unit there. The
three factors of `w'` in the denominator against one in the numerator are `ord(dt) = −3`. -/
theorem family_infinity_D_relation :
    (quadT (familyH m (star α)) ^ 2 *
          algebraMap ℂ[X] (QuadField (familyH m (star α))) (familyH m (star α)).derivative) •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (familyInfinityAlgEquiv m α (quadT (familyH m α))) =
      (-(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (AdjoinRoot.root (quadRat (familyH m (star α)))) := by
  have hs := quadT_ne_zero (familyH m (star α))
  have h2f := quad_ramified_coeff (familyH m (star α)) 1
  rw [one_smul] at h2f
  rw [familyInfinityAlgEquiv_quadT, Derivation.leibniz_inv, smul_smul]
  have hcoef : quadT (familyH m (star α)) ^ 2 *
      algebraMap ℂ[X] (QuadField (familyH m (star α))) (familyH m (star α)).derivative *
        -(quadT (familyH m (star α)))⁻¹ ^ 2 =
      -(algebraMap ℂ[X] (QuadField (familyH m (star α))) (familyH m (star α)).derivative) := by
    field_simp
  rw [hcoef, neg_smul, h2f, ← neg_smul]
  congr 1
  ring

/-- The conjugate place that reads infinity is ramified: `w'` generates its maximal ideal
and `h_conj'(s)` is a unit there. -/
theorem family_infinity_conjugate_ramified :
    IsLocalRing.maximalIdeal (quadLocalRing (familyH m (star α)) 0 0
          (familyH_star_zero_point m α)) =
        Ideal.span {algebraMap (QuadRing (familyH m (star α)))
          (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
          (AdjoinRoot.root (quadPoly (familyH m (star α))))} ∧
      IsUnit (algebraMap (QuadRing (familyH m (star α)))
        (quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
        (algebraMap ℂ[X] (QuadRing (familyH m (star α)))
          (familyH m (star α)).derivative)) ∧
      ∃ k : ℂ[X], k.eval 0 ≠ 0 ∧
        quadShift (familyH m (star α)) 0 *
            algebraMap ℂ[X] (QuadRing (familyH m (star α))) k =
          AdjoinRoot.root (quadPoly (familyH m (star α))) ^ 2 :=
  ⟨quad_ramified_uniformizer _ 0 0 (familyH_star_zero_point m α) (familyH_eval_zero m (star α)),
    quad_ramified_derivative_isUnit _ 0 0 (familyH_star_zero_point m α)
      (familyH_eval_zero m (star α)),
    quad_ramified_shift_sq _ 0 (familyH_eval_zero m (star α))⟩

#print axioms familyInfinityAlgEquiv
#print axioms family_infinity_differential_spans
#print axioms family_infinity_D_relation

end CurveSymmetry
