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
`φ(f)·(−2w')/(s²·h_conj'(s))`, by G09a-2g. `isRegularAtInfinity_iff_cube`
(G09b-3a) cancels the units `2`, `h_conj'(s)` and the `k` of `s·k = w'²`: `f·dt`
is regular at infinity exactly when `φ(f)/w'³` lies in the local ring, that is,
when `φ(f)` vanishes to order at least three there.
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

/-- In the conjugate function field, `s·k = w'²` for a `k` that is a unit at `(0, 0)`. -/
lemma familyInfinity_shift_sq :
    ∃ k : ℂ[X], k.eval 0 ≠ 0 ∧
      quadT (familyH m (star α)) * algebraMap ℂ[X] (QuadField (familyH m (star α))) k =
        AdjoinRoot.root (quadRat (familyH m (star α))) ^ 2 := by
  obtain ⟨k, hk0, hks⟩ := quad_ramified_shift_sq (familyH m (star α)) 0
    (familyH_eval_zero m (star α))
  refine ⟨k, hk0, ?_⟩
  set h' := familyH m (star α)
  have hmap := congrArg (algebraMap (QuadRing h') (QuadField h')) hks
  rw [map_mul, map_pow] at hmap
  have h1 : algebraMap (QuadRing h') (QuadField h') (quadShift h' 0) = quadT h' := by
    rw [quadShift, ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h'),
      C_0, sub_zero]
    rfl
  have h2 : algebraMap (QuadRing h') (QuadField h') (algebraMap ℂ[X] (QuadRing h') k) =
      algebraMap ℂ[X] (QuadField h') k :=
    (IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h') k).symm
  have h3 : algebraMap (QuadRing h') (QuadField h') (AdjoinRoot.root (quadPoly h')) =
      AdjoinRoot.root (quadRat h') := by
    rw [algebraMap_quadRing_apply, quadRingMap_root]
  rw [h1, h2, h3] at hmap
  exact hmap

/-- **G09b-3a**: `f·dt` is regular at the place over `t = ∞` exactly when `φ(f)/w'³` lies
in the local ring of the conjugate point place `(0, 0)`: `f` must vanish to order three
there. -/
theorem isRegularAtInfinity_iff_cube (f : QuadField (familyH m α)) :
    IsRegularAtInfinity (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
        (quadT (familyH m α))) ↔
      familyInfinityMap m α f * (AdjoinRoot.root (quadRat (familyH m (star α))) ^ 3)⁻¹ ∈
        quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) := by
  set h' := familyH m (star α) with hh'
  set O := quadLocalRing h' 0 0 (familyH_star_zero_point m α)
  set s := quadT h'
  set w := AdjoinRoot.root (quadRat h')
  set hp := algebraMap ℂ[X] (QuadField h') h'.derivative
  obtain ⟨k₀, hk0, hsk⟩ := familyInfinity_shift_sq (m := m) (α := α)
  set k := algebraMap ℂ[X] (QuadField h') k₀
  have hc0 := familyH_eval_zero m (star α)
  have hw : w ≠ 0 := quadRoot_ne_zero h'
  have hs : s ≠ 0 := quadT_ne_zero h'
  have hk : k ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsk
    exact hw (pow_eq_zero_iff two_ne_zero |>.mp hsk.symm)
  have hpne : hp ≠ 0 := quad_derivative_ne_zero h' 0 hc0
  obtain ⟨hkmem, hkinv⟩ := quadLocal_poly_unit h' 0 0 (familyH_star_zero_point m α) k₀ hk0
  have hpmem : hp ∈ O := by
    have : hp = algebraMap (QuadRing h') (QuadField h')
        (algebraMap ℂ[X] (QuadRing h') h'.derivative) := by
      rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h')]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  have hpinv : hp⁻¹ ∈ O := by
    have : hp = algebraMap (QuadRing h') (QuadField h')
        (algebraMap ℂ[X] (QuadRing h') h'.derivative) := by
      rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h') (QuadField h')]
    rw [this]
    exact quadLocal_inv_mem_of_isUnit h' 0 0 (familyH_star_zero_point m α)
      (quad_ramified_derivative_isUnit h' 0 0 (familyH_star_zero_point m α) hc0)
  have htwo : (2 : QuadField h') ∈ O := by
    rw [show (2 : QuadField h') = algebraMap ℂ (QuadField h') 2 from
      (map_ofNat (algebraMap ℂ (QuadField h')) 2).symm]
    exact quadLocal_const_mem h' 0 0 (familyH_star_zero_point m α) 2
  have htwoinv : (2 : QuadField h')⁻¹ ∈ O := by
    rw [show (2 : QuadField h')⁻¹ = algebraMap ℂ (QuadField h') 2⁻¹ by
      rw [map_inv₀, map_ofNat]]
    exact quadLocal_const_mem h' 0 0 (familyH_star_zero_point m α) _
  -- the unit relating the raw coefficient to `φ(f)/w'³`
  set e := -(2 * k ^ 2) * hp⁻¹ with he
  set e' := -(hp * k⁻¹ ^ 2 * 2⁻¹) with he'
  have hemem : e ∈ O :=
    Subalgebra.mul_mem _ (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ htwo
      (Subalgebra.pow_mem _ hkmem 2))) hpinv
  have he'mem : e' ∈ O :=
    Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hpmem
      (Subalgebra.pow_mem _ hkinv 2)) htwoinv)
  have hee : e * e' = 1 := by
    rw [he, he']
    calc -(2 * k ^ 2) * hp⁻¹ * -(hp * k⁻¹ ^ 2 * 2⁻¹)
        = (2 * 2⁻¹) * (k * k⁻¹) ^ 2 * (hp⁻¹ * hp) := by ring
      _ = 1 := by
        rw [mul_inv_cancel₀ two_ne_zero, mul_inv_cancel₀ hk, inv_mul_cancel₀ hpne]
        ring
  have hsval : s = w ^ 2 * k⁻¹ := by
    rw [← hsk, mul_assoc, mul_inv_cancel₀ hk, mul_one]
  have hraw : familyInfinityMap m α f * ((s ^ 2 * hp)⁻¹ * -(2 * w)) =
      e * (familyInfinityMap m α f * (w ^ 3)⁻¹) := by
    rw [hsval, he]
    field_simp
  rw [isRegularAtInfinity_iff, hraw]
  exact (quadLocal_mem_mul_iff h' 0 0 (familyH_star_zero_point m α) hemem he'mem hee).symm

#print axioms IsRegularAtInfinity
#print axioms isRegularAtInfinity_iff
#print axioms isRegularAtInfinity_iff_cube

end CurveSymmetry
