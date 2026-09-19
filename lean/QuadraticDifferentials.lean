import QuadraticDedekind
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Differentials of the quadratic double cover (G09a-1)

The differentials `Ω[K⁄ℂ]` of `K = ℂ(t)[w]/(w² − h)` form a one-dimensional
`K`-vector space spanned by `dt`.

The two steps are base changes along formally étale maps: `ℂ(t)` is a
localization of `ℂ[t]`, and `K` is separable over `ℂ(t)` because `ℂ(t)` has
characteristic zero. Each step transports a basis, starting from the free
rank-one module `Ω[ℂ[t]⁄ℂ]` of Mathlib's `polynomialEquiv`.

Nothing here defines an order of vanishing or a genus; G09a-2 computes
`ord_v(dt)` at the places of G07b, for which `quad_D_root` provides the
relation `2w·dw = h'(t)·dt`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial TensorProduct

section BaseChange

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T] {ι : Type*} [Unique ι]

/-- A basis of `Ω[S⁄R]` transported along a formally étale `S → T`. -/
noncomputable def kaehlerBasisOfEtale (b : Module.Basis ι S Ω[S⁄R]) : Module.Basis ι T Ω[T⁄R] :=
  (b.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T)

omit [Unique ι] in
@[simp] lemma kaehlerBasisOfEtale_apply (b : Module.Basis ι S Ω[S⁄R]) (i : ι) :
    kaehlerBasisOfEtale R S T b i = KaehlerDifferential.map R R S T (b i) := by
  simp [kaehlerBasisOfEtale, Module.Basis.baseChange_apply,
    KaehlerDifferential.mapBaseChange_tmul]

end BaseChange

/-- `Ω[ℂ[t]⁄ℂ]` is free of rank one on `dt`. -/
noncomputable def polynomialKaehlerBasis : Module.Basis Unit ℂ[X] Ω[ℂ[X]⁄ℂ] :=
  (Module.Basis.singleton Unit ℂ[X]).map (KaehlerDifferential.polynomialEquiv ℂ).symm

@[simp] lemma polynomialKaehlerBasis_apply (i : Unit) :
    polynomialKaehlerBasis i = KaehlerDifferential.D ℂ ℂ[X] X := by
  simp [polynomialKaehlerBasis, Module.Basis.singleton_apply,
    KaehlerDifferential.polynomialEquiv_symm]

/-- `ℂ(t)` is a localization of `ℂ[t]`, hence formally étale over it. -/
instance ratFunc_formallyEtale : Algebra.FormallyEtale ℂ[X] (RatFunc ℂ) :=
  Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors ℂ[X])

/-- `Ω[ℂ(t)⁄ℂ]` is free of rank one on `dt`. -/
noncomputable def ratFuncKaehlerBasis : Module.Basis Unit (RatFunc ℂ) Ω[RatFunc ℂ⁄ℂ] :=
  kaehlerBasisOfEtale ℂ ℂ[X] (RatFunc ℂ) polynomialKaehlerBasis

@[simp] lemma ratFuncKaehlerBasis_apply (i : Unit) :
    ratFuncKaehlerBasis i = KaehlerDifferential.D ℂ (RatFunc ℂ) RatFunc.X := by
  rw [ratFuncKaehlerBasis, kaehlerBasisOfEtale_apply, polynomialKaehlerBasis_apply,
    KaehlerDifferential.map_D, RatFunc.algebraMap_X]

section Quad

variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]

/-- The coordinate `t` of the base line, inside the quadratic extension. -/
noncomputable def quadT : QuadField h := algebraMap ℂ[X] (QuadField h) X

lemma quadT_eq : quadT h = algebraMap (RatFunc ℂ) (QuadField h) RatFunc.X := by
  rw [quadT, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]

/-- Characteristic zero makes the quadratic extension separable, hence formally étale. -/
instance quadField_formallyEtale : Algebra.FormallyEtale (RatFunc ℂ) (QuadField h) :=
  Algebra.FormallyEtale.of_isSeparable _ _

/-- **G09a-1**: `Ω[K⁄ℂ]` is free of rank one on `dt`. -/
noncomputable def quadKaehlerBasis : Module.Basis Unit (QuadField h) Ω[QuadField h⁄ℂ] :=
  kaehlerBasisOfEtale ℂ (RatFunc ℂ) (QuadField h) ratFuncKaehlerBasis

@[simp] lemma quadKaehlerBasis_apply (i : Unit) :
    quadKaehlerBasis h i = KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  rw [quadKaehlerBasis, kaehlerBasisOfEtale_apply, ratFuncKaehlerBasis_apply,
    KaehlerDifferential.map_D, quadT_eq]

theorem quad_kaehler_span_eq_top :
    Submodule.span (QuadField h) {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} = ⊤ := by
  have hrange : Set.range (quadKaehlerBasis h) =
      {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} := by
    rw [Set.range_unique, quadKaehlerBasis_apply]
  rw [← hrange]
  exact (quadKaehlerBasis h).span_eq

theorem quad_D_t_ne_zero : KaehlerDifferential.D ℂ (QuadField h) (quadT h) ≠ 0 := by
  have := (quadKaehlerBasis h).ne_zero (default : Unit)
  rwa [quadKaehlerBasis_apply] at this

theorem quad_kaehler_finrank : Module.finrank (QuadField h) Ω[QuadField h⁄ℂ] = 1 := by
  rw [Module.finrank_eq_card_basis (quadKaehlerBasis h), Fintype.card_unit]

/-- A differential that spans is nonzero, because the space is one-dimensional. -/
theorem quad_D_ne_zero_of_span {x : QuadField h}
    (hspan : Submodule.span (QuadField h) {KaehlerDifferential.D ℂ (QuadField h) x} = ⊤) :
    KaehlerDifferential.D ℂ (QuadField h) x ≠ 0 := by
  intro hzero
  rw [hzero, Submodule.span_singleton_eq_bot.mpr rfl] at hspan
  haveI : Subsingleton Ω[QuadField h⁄ℂ] := by
    constructor
    intro y z
    have hy : y ∈ (⊥ : Submodule (QuadField h) Ω[QuadField h⁄ℂ]) := by rw [hspan]; trivial
    have hz : z ∈ (⊥ : Submodule (QuadField h) Ω[QuadField h⁄ℂ]) := by rw [hspan]; trivial
    rw [Submodule.mem_bot] at hy hz
    rw [hy, hz]
  have hfin := quad_kaehler_finrank h
  rw [Module.finrank_eq_zero_of_subsingleton] at hfin
  exact zero_ne_one hfin

/-- Every differential is a multiple of `dt`. -/
theorem quad_exists_smul_D_t (ω : Ω[QuadField h⁄ℂ]) :
    ∃ c : QuadField h, ω = c • KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hmem : ω ∈ Submodule.span (QuadField h)
      {KaehlerDifferential.D ℂ (QuadField h) (quadT h)} := by
    rw [quad_kaehler_span_eq_top]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, hc.symm⟩

/-- The chain rule along `ℂ[t] → K`. -/
theorem quad_D_algebraMap (p : ℂ[X]) :
    KaehlerDifferential.D ℂ (QuadField h) (algebraMap ℂ[X] (QuadField h) p) =
      algebraMap ℂ[X] (QuadField h) p.derivative •
        KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hae : ∀ q : ℂ[X], aeval (quadT h) q = algebraMap ℂ[X] (QuadField h) q := by
    intro q
    rw [quadT, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [← hae p, (KaehlerDifferential.D ℂ (QuadField h)).map_aeval p (quadT h), hae]

/-- `w² = h(t)` differentiates to `2w·dw = h'(t)·dt`. -/
theorem quad_D_root :
    (2 * AdjoinRoot.root (quadRat h)) •
        KaehlerDifferential.D ℂ (QuadField h) (AdjoinRoot.root (quadRat h)) =
      algebraMap ℂ[X] (QuadField h) h.derivative •
        KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hsq : AdjoinRoot.root (quadRat h) ^ 2 = algebraMap ℂ[X] (QuadField h) h := by
    rw [quadRoot_sq, ← IsScalarTower.algebraMap_apply]
  have hleft := (KaehlerDifferential.D ℂ (QuadField h)).leibniz_pow
    (a := AdjoinRoot.root (quadRat h)) 2
  rw [hsq, quad_D_algebraMap] at hleft
  rw [hleft]
  simp [pow_one, two_smul, two_mul, add_smul]

end Quad

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- G09a-1 for the family: the differentials of the function field of `V_α` form a
one-dimensional space over that field, spanned by `dt`. Orders of vanishing and
the genus are not defined here. -/
theorem family_kaehler_dt :
    Module.finrank (QuadField (familyH m α)) Ω[QuadField (familyH m α)⁄ℂ] = 1 ∧
      Submodule.span (QuadField (familyH m α))
          {KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))} = ⊤ :=
  ⟨quad_kaehler_finrank _, quad_kaehler_span_eq_top _⟩

#print axioms quad_kaehler_finrank
#print axioms quad_D_root
#print axioms family_kaehler_dt

end CurveSymmetry
