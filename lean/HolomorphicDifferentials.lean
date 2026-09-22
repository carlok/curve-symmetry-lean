import PlaceUniformizers

/-!
# Regularity of a differential at a point place (G09b-1)

A differential is regular at a place when the coefficient against a uniformizer
lies in the local ring. By G09a-2c this does not depend on the uniformizer, so
the definition quantifies over all of them and `isRegularAt_iff` reads it off
from any single one.

At the two kinds of point place the criterion becomes explicit, using the
uniformizers of G09a-2e and G09a-2f:

* `h(c) ≠ 0`: `f·dt` is regular exactly when `f` is in the local ring;
* `h(c) = 0`: exactly when `f·w` is, one pole of `f` being allowed.

The place at infinity, the holomorphic differentials as a space, and the genus
are not treated here.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

instance quadField_charZero : CharZero (QuadField h) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (QuadField h)).injective

/-- A differential is regular at the point place `(c, d)` when its coefficient against a
uniformizer there lies in the local ring. -/
def IsRegularAt (ω : Ω[QuadField h⁄ℂ]) : Prop :=
  ∀ (u : quadLocalRing h c d hd) (f : QuadField h),
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u} →
      ω = f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) →
        f ∈ quadLocalRing h c d hd

/-- One uniformizer decides regularity. -/
theorem isRegularAt_iff {u : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u})
    {ω : Ω[QuadField h⁄ℂ]} {f : QuadField h}
    (hf : ω = f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h)) :
    IsRegularAt h c d hd ω ↔ f ∈ quadLocalRing h c d hd := by
  constructor
  · intro hreg
    exact hreg u f hu hf
  · intro hfmem u' f' hu' hf'
    obtain ⟨e, he, -, hfe⟩ := quadLocal_coeff_unit h c d hd hu' hu hf' hf
    rw [hfe]
    exact Subalgebra.mul_mem _ he hfmem

/-- Constants lie in every point place's local ring. -/
lemma quadLocal_const_mem (z : ℂ) :
    algebraMap ℂ (QuadField h) z ∈ quadLocalRing h c d hd := by
  have : algebraMap ℂ (QuadField h) z =
      algebraMap (QuadRing h) (QuadField h) (algebraMap ℂ (QuadRing h) z) := by
    rw [← IsScalarTower.algebraMap_apply ℂ (QuadRing h) (QuadField h)]
  rw [this]
  exact Subalgebra.algebraMap_mem _ _

/-- Multiplying by a unit of the local ring does not change membership. -/
lemma quadLocal_mem_mul_iff {e e' x : QuadField h} (he : e ∈ quadLocalRing h c d hd)
    (he' : e' ∈ quadLocalRing h c d hd) (hee : e * e' = 1) :
    x ∈ quadLocalRing h c d hd ↔ e * x ∈ quadLocalRing h c d hd := by
  constructor
  · intro hx
    exact Subalgebra.mul_mem _ he hx
  · intro hx
    have : x = e' * (e * x) := by
      rw [← mul_assoc, mul_comm e' e, hee, one_mul]
    rw [this]
    exact Subalgebra.mul_mem _ he' hx

/-- **G09b-1, unramified case**: `f·dt` is regular at a place with `h(c) ≠ 0` exactly when
`f` lies in its local ring. -/
theorem isRegularAt_unramified (hc : h.eval c ≠ 0) (f : QuadField h) :
    IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h)) ↔
      f ∈ quadLocalRing h c d hd :=
  isRegularAt_iff h c d hd (quad_unramified_uniformizer h c d hd hc)
    (by rw [quad_unramified_D_uniformizer])

/-- At a ramified place the derivative of `h` is a nonzero element of the function field. -/
lemma quad_derivative_ne_zero (hc : h.eval c = 0) :
    algebraMap ℂ[X] (QuadField h) h.derivative ≠ 0 := by
  have hderiv : h.derivative ≠ 0 := by
    intro hzero
    have hC := Polynomial.eq_C_of_derivative_eq_zero hzero
    have h0 : h.coeff 0 = 0 := by
      have := hc
      rw [hC, eval_C] at this
      exact this
    have : h = 0 := by rw [hC, h0, map_zero]
    exact (Fact.out : Squarefree h).ne_zero this
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
    (RatFunc.algebraMap_ne_zero hderiv)

/-- An element that becomes a unit of the local ring has its inverse there. -/
lemma quadLocal_inv_mem_of_isUnit {x : QuadRing h}
    (hx : IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd) x)) :
    (algebraMap (QuadRing h) (QuadField h) x)⁻¹ ∈ quadLocalRing h c d hd := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have hcoe : algebraMap (QuadRing h) (QuadField h) x * (y : QuadField h) = 1 := by
    have hc1 := congrArg (fun z : quadLocalRing h c d hd => (z : QuadField h)) hy
    simpa using hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact y.2

/-- A polynomial in `t` that does not vanish at `c` is a unit of the local ring at any point
place over `c`: it and its inverse both lie there. -/
lemma quadLocal_poly_unit (p : ℂ[X]) (hp : p.eval c ≠ 0) :
    algebraMap ℂ[X] (QuadField h) p ∈ quadLocalRing h c d hd ∧
      (algebraMap ℂ[X] (QuadField h) p)⁻¹ ∈ quadLocalRing h c d hd := by
  have htower : algebraMap ℂ[X] (QuadField h) p =
      algebraMap (QuadRing h) (QuadField h) (algebraMap ℂ[X] (QuadRing h) p) := by
    rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
  have hmem : algebraMap ℂ[X] (QuadRing h) p ∈ (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_algebraMap]
    exact hp
  refine ⟨?_, ?_⟩
  · rw [htower]
    exact Subalgebra.algebraMap_mem _ _
  · rw [htower]
    exact quadLocal_inv_mem_of_isUnit h c d hd
      (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hmem⟩)

/-- The root `w` is nonzero in the function field: `w² = h ≠ 0`. -/
lemma quadRoot_ne_zero : AdjoinRoot.root (quadRat h) ≠ 0 := by
  intro hzero
  have hsq := quadRoot_sq h
  rw [hzero, zero_pow two_ne_zero] at hsq
  have hne : algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) h) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      (RatFunc.algebraMap_ne_zero (Fact.out : Squarefree h).ne_zero)
  exact hne hsq.symm

/-- **G09b-1, ramified case**: `f·dt` is regular at a place with `h(c) = 0` exactly when
`f·w` lies in its local ring: `f` may have one pole there. -/
theorem isRegularAt_ramified (hc : h.eval c = 0) (f : QuadField h) :
    IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h)) ↔
      f * AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
  have hderiv := quad_derivative_ne_zero h c hc
  have hrel := quad_ramified_coeff h f
  have hcoeff : f • KaehlerDifferential.D ℂ (QuadField h) (quadT h) =
      ((algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ *
          (2 * f * AdjoinRoot.root (quadRat h))) •
        KaehlerDifferential.D ℂ (QuadField h) (AdjoinRoot.root (quadRat h)) := by
    conv_rhs => rw [← smul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hderiv, one_smul]
  rw [isRegularAt_iff h c d hd (quad_ramified_uniformizer h c d hd hc)
    (by rw [quad_ramified_uniformizer_coe]; exact hcoeff)]
  have htower : algebraMap ℂ[X] (QuadField h) h.derivative =
      algebraMap (QuadRing h) (QuadField h)
        (algebraMap ℂ[X] (QuadRing h) h.derivative) := by
    rw [← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
  have hpmem : algebraMap ℂ[X] (QuadField h) h.derivative ∈ quadLocalRing h c d hd := by
    rw [htower]
    exact Subalgebra.algebraMap_mem _ _
  have hinvmem : (algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ ∈
      quadLocalRing h c d hd := by
    rw [htower]
    exact quadLocal_inv_mem_of_isUnit h c d hd (quad_ramified_derivative_isUnit h c d hd hc)
  have htwo : (2 : QuadField h) = algebraMap ℂ (QuadField h) 2 :=
    (map_ofNat (algebraMap ℂ (QuadField h)) 2).symm
  have htwoinv : (2 : QuadField h)⁻¹ = algebraMap ℂ (QuadField h) 2⁻¹ := by
    rw [htwo, ← map_inv₀]
  constructor
  · intro hmem
    have hfac : f * AdjoinRoot.root (quadRat h) =
        (algebraMap ℂ[X] (QuadField h) h.derivative * 2⁻¹) *
          ((algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ *
            (2 * f * AdjoinRoot.root (quadRat h))) := by
      field_simp
    rw [hfac]
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hpmem ?_) hmem
    rw [htwoinv]
    exact quadLocal_const_mem h c d hd _
  · intro hmem
    have hfac : (algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ *
        (2 * f * AdjoinRoot.root (quadRat h)) =
        ((algebraMap ℂ[X] (QuadField h) h.derivative)⁻¹ * 2) *
          (f * AdjoinRoot.root (quadRat h)) := by
      ring
    rw [hfac]
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hinvmem ?_) hmem
    rw [htwo]
    exact quadLocal_const_mem h c d hd _


end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- G09b-1 for the family: the regularity criterion for `f·dt` at each kind of point place
of the family's double cover. -/
theorem family_isRegularAt_criteria (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
    (f : QuadField (familyH m α)) :
    ((familyH m α).eval c ≠ 0 →
        (IsRegularAt (familyH m α) c d hd
            (f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))) ↔
          f ∈ quadLocalRing (familyH m α) c d hd)) ∧
      ((familyH m α).eval c = 0 →
        (IsRegularAt (familyH m α) c d hd
            (f • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))) ↔
          f * AdjoinRoot.root (quadRat (familyH m α)) ∈ quadLocalRing (familyH m α) c d hd)) :=
  ⟨fun hc => isRegularAt_unramified _ c d hd hc f,
    fun hc => isRegularAt_ramified _ c d hd hc f⟩

#print axioms isRegularAt_unramified
#print axioms isRegularAt_ramified
#print axioms family_isRegularAt_criteria

end CurveSymmetry
