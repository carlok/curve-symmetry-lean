import HolomorphicDifferentials
import InfinityDifferentials

/-!
# Regularity of a differential at the place over `t = ∞` (G09b-2)

The chart isomorphism of G07b-3 is an isomorphism of `ℂ`-algebras (G09a-2d), so
it carries differentials of the function field to differentials of the conjugate
family's function field, and carries the place over `t = ∞` to the point place
`(0, 0)`. Regularity at infinity is therefore defined as regularity of the
transported differential at that point place, where G09b-1 applies.

For `f·dt` the transported differential is computed here in closed form: the
coefficient against the uniformizer `w'` is
`φ(f)·(−2w')/(s²·h_conj'(s))`, by G09a-2g. Simplifying that to the expected
`ord(φ f) ≥ 3` needs the units `2`, `h_conj'(s)` and `k` to be cancelled, which
is left to G09b-3 together with the basis.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- A differential is regular at the place over `t = ∞` when its transport along the chart
isomorphism is regular at the conjugate family's point place `(0, 0)`. -/
def IsRegularAtInfinity (ω : Ω[QuadField (familyH m α)⁄ℂ]) : Prop :=
  IsRegularAt (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
    (kaehlerTransport (familyInfinityAlgEquiv m α) ω)

/-- The transport of `f·dt` is `φ(f)·d(1/s)`. -/
lemma kaehlerTransport_smul_D_quadT (f : QuadField (familyH m α)) :
    kaehlerTransport (familyInfinityAlgEquiv m α)
        (f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))) =
      familyInfinityMap m α f •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (quadT (familyH m (star α)))⁻¹ := by
  rw [kaehlerTransport_smul, kaehlerTransport_D, familyInfinityAlgEquiv_quadT,
    familyInfinityAlgEquiv_apply]

/-- **G09b-2**: `f·dt` is regular at the place over `t = ∞` exactly when the coefficient
`φ(f)·(−2w')/(s²·h_conj'(s))` lies in the local ring of the conjugate point place. -/
theorem isRegularAtInfinity_iff (f : QuadField (familyH m α)) :
    IsRegularAtInfinity (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
        (quadT (familyH m α))) ↔
      familyInfinityMap m α f *
          ((quadT (familyH m (star α)) ^ 2 *
            algebraMap ℂ[X] (QuadField (familyH m (star α)))
              (familyH m (star α)).derivative)⁻¹ *
            -(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) ∈
        quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) := by
  have hs := quadT_ne_zero (familyH m (star α))
  have hderiv := quad_derivative_ne_zero (familyH m (star α)) 0 (familyH_eval_zero m (star α))
  have hprod : quadT (familyH m (star α)) ^ 2 *
      algebraMap ℂ[X] (QuadField (familyH m (star α)))
        (familyH m (star α)).derivative ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hs) hderiv
  -- `d(1/s)` against the uniformizer `w'`
  have hD : KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
        (quadT (familyH m (star α)))⁻¹ =
      ((quadT (familyH m (star α)) ^ 2 *
          algebraMap ℂ[X] (QuadField (familyH m (star α)))
            (familyH m (star α)).derivative)⁻¹ *
          -(2 * AdjoinRoot.root (quadRat (familyH m (star α))))) •
        KaehlerDifferential.D ℂ (QuadField (familyH m (star α)))
          (AdjoinRoot.root (quadRat (familyH m (star α)))) := by
    have hrel := family_infinity_D_relation (m := m) (α := α)
    rw [familyInfinityAlgEquiv_quadT] at hrel
    conv_rhs => rw [← smul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hprod, one_smul]
  rw [IsRegularAtInfinity, kaehlerTransport_smul_D_quadT, hD, smul_smul]
  exact isRegularAt_iff (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
    (quad_ramified_uniformizer _ 0 0 (familyH_star_zero_point m α)
      (familyH_eval_zero m (star α)))
    (by rw [quad_ramified_uniformizer_coe])

#print axioms IsRegularAtInfinity
#print axioms isRegularAtInfinity_iff

end CurveSymmetry
