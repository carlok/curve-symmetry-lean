import QuadraticDifferentials
import Fermat
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Kummer covers `yⁿ = f(x)` (R01c-1)

R01 compares the family (a double cover, G07–G09) with the quartic
`X⁴ + Y⁴ = 2`, which in the coordinates `x = X`, `y = Y` is the degree-four
Kummer cover `y⁴ = 2 − x⁴` of the `x`-line. This module sets up the Kummer cover
`yⁿ = f` for a squarefree `f`, in the pattern of the quadratic modules:

* `KummerRing n f = ℂ[x][Y]/(Yⁿ − f)` and `KummerField n f = ℂ(x)[Y]/(Yⁿ − f)`;
* `Yⁿ − f` is irreducible when `f` is squarefree and not constant: Eisenstein at a
  simple root of `f` (`kummerPoly_irreducible`), then Gauss's lemma
  (`kummerRat_irreducible`);
* the ring embeds in the field (`kummerRingMap_injective`), by division by the
  monic `Yⁿ − f`;
* `Ω[K⁄ℂ]` is one-dimensional over `K`, spanned by `dx` (`kummerKaehlerBasis`), by
  the two formally étale base changes of G09a-1, and `n·yⁿ⁻¹·dy = f'(x)·dx`
  (`kummer_D_root`).

For the quartic, `fermatNested 4` is literally `kummerPoly 4 (2 − x⁴)`, so its
irreducibility comes from `fermatNested_irreducible`. Places, regularity and the
genus of the quartic are R01d and later.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

/-- `Yⁿ − f` over `ℂ[x]`. -/
noncomputable def kummerPoly (n : ℕ) (f : ℂ[X]) : ℂ[X][X] := X ^ n - C f

/-- The affine coordinate ring `ℂ[x][Y]/(Yⁿ − f)` of the Kummer cover. -/
abbrev KummerRing (n : ℕ) (f : ℂ[X]) : Type := AdjoinRoot (kummerPoly n f)

/-- `Yⁿ − f` over `ℂ(x)`. -/
noncomputable def kummerRat (n : ℕ) (f : ℂ[X]) : (RatFunc ℂ)[X] :=
  X ^ n - C (algebraMap ℂ[X] (RatFunc ℂ) f)

/-- The function field `ℂ(x)[Y]/(Yⁿ − f)` of the Kummer cover. -/
abbrev KummerField (n : ℕ) (f : ℂ[X]) : Type := AdjoinRoot (kummerRat n f)

section Polynomials

variable (n : ℕ) (f : ℂ[X])

lemma kummerPoly_monic (hn : n ≠ 0) : (kummerPoly n f).Monic := monic_X_pow_sub_C _ hn

lemma kummerRat_monic (hn : n ≠ 0) : (kummerRat n f).Monic := monic_X_pow_sub_C _ hn

lemma kummerPoly_map :
    (kummerPoly n f).map (algebraMap ℂ[X] (RatFunc ℂ)) = kummerRat n f := by
  simp [kummerPoly, kummerRat, Polynomial.map_sub, Polynomial.map_pow]

/-- **R01c-1**: for squarefree, nonconstant `f`, the polynomial `Yⁿ − f` is irreducible over
`ℂ[x]`, by Eisenstein's criterion at a simple root of `f`. -/
theorem kummerPoly_irreducible (hn : n ≠ 0) (hsq : Squarefree f) (hf : 0 < f.natDegree) :
    Irreducible (kummerPoly n f) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_root f (natDegree_pos_iff_degree_pos.mp hf).ne'
  have hmonic := kummerPoly_monic n f hn
  have hdeg : (kummerPoly n f).natDegree = n := natDegree_X_pow_sub_C
  have hprime : (Ideal.span {X - C c} : Ideal ℂ[X]).IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero c)).mpr (prime_X_sub_C c)
  apply irreducible_of_eisenstein_criterion hprime
  · rw [hmonic.leadingCoeff]
    exact fun h => hprime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  · intro k hk
    have hk' : k < n := by simpa [hdeg] using coe_lt_degree.mp hk
    rw [Ideal.mem_span_singleton]
    simp only [kummerPoly, coeff_sub, coeff_X_pow, coeff_C, ite_eq_right hk'.ne]
    by_cases h0 : k = 0
    · rw [ite_eq_left h0, zero_sub, dvd_neg]
      exact dvd_iff_isRoot.mpr hc
    · rw [ite_eq_right h0, sub_zero]
      exact dvd_zero _
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [kummerPoly, coeff_sub, coeff_X_pow, coeff_C, ite_eq_right (Ne.symm hn),
      zero_sub, dvd_neg]
    intro hdvd
    exact not_isUnit_X_sub_C c (hsq _ (by rwa [← sq]))
  · exact hmonic.isPrimitive

/-- `Yⁿ − f` stays irreducible over `ℂ(x)` (Gauss's lemma). -/
theorem kummerRat_irreducible (hn : n ≠ 0) (hsq : Squarefree f) (hf : 0 < f.natDegree) :
    Irreducible (kummerRat n f) := by
  rw [← kummerPoly_map]
  exact (kummerPoly_monic n f hn).irreducible_iff_irreducible_map_fraction_map.mp
    (kummerPoly_irreducible n f hn hsq hf)

end Polynomials

section Ring

variable (n : ℕ) (f : ℂ[X])

/-- The comparison map from the coordinate ring to the function field, `Y ↦ y`. -/
noncomputable def kummerRingMap : KummerRing n f →ₐ[ℂ[X]] KummerField n f :=
  AdjoinRoot.liftAlgHom (kummerPoly n f) (Algebra.ofId ℂ[X] (KummerField n f))
    (AdjoinRoot.root (kummerRat n f)) (by
      change eval₂ (algebraMap ℂ[X] (KummerField n f)) _ _ = 0
      rw [← aeval_def, ← Polynomial.aeval_map_algebraMap (RatFunc ℂ), kummerPoly_map,
        AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])

lemma kummerRingMap_mk (g : ℂ[X][X]) :
    kummerRingMap n f (AdjoinRoot.mk (kummerPoly n f) g) =
      AdjoinRoot.mk (kummerRat n f) (g.map (algebraMap ℂ[X] (RatFunc ℂ))) := by
  conv_rhs => rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_map_algebraMap]
  rw [kummerRingMap, AdjoinRoot.liftAlgHom_mk, aeval_def]
  rfl

lemma kummerRingMap_root :
    kummerRingMap n f (AdjoinRoot.root (kummerPoly n f)) = AdjoinRoot.root (kummerRat n f) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- **R01c-1**: the coordinate ring embeds in the function field. -/
theorem kummerRingMap_injective (hn : n ≠ 0) : Function.Injective (kummerRingMap n f) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using AdjoinRoot.induction_on with
  | ih g =>
    have hmon := kummerPoly_monic n f hn
    rw [kummerRingMap_mk, AdjoinRoot.mk_eq_zero, ← kummerPoly_map,
      ← modByMonic_eq_zero_iff_dvd (hmon.map _), ← map_modByMonic _ hmon] at hx
    rw [AdjoinRoot.mk_eq_zero, ← modByMonic_eq_zero_iff_dvd hmon]
    exact Polynomial.map_injective _ (IsFractionRing.injective ℂ[X] (RatFunc ℂ))
      (hx.trans (Polynomial.map_zero _).symm)

end Ring

section Field

variable (n : ℕ) (f : ℂ[X]) [Fact (Irreducible (kummerRat n f))]

instance kummerField_finiteDimensional : FiniteDimensional (RatFunc ℂ) (KummerField n f) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible (kummerRat n f)).ne_zero).finite

/-- The coordinate `x` of the base line, inside the function field. -/
noncomputable def kummerX : KummerField n f := algebraMap ℂ[X] (KummerField n f) X

lemma kummerX_eq : kummerX n f = algebraMap (RatFunc ℂ) (KummerField n f) RatFunc.X := by
  rw [kummerX, IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (KummerField n f),
    RatFunc.algebraMap_X]

/-- The defining relation `yⁿ = f(x)`. -/
lemma kummerRoot_pow :
    AdjoinRoot.root (kummerRat n f) ^ n = algebraMap ℂ[X] (KummerField n f) f := by
  have h0 : AdjoinRoot.mk (kummerRat n f)
      (X ^ n - C (algebraMap ℂ[X] (RatFunc ℂ) f)) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
  rw [h0, ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/-- Characteristic zero makes the extension separable, hence formally étale. -/
instance kummerField_formallyEtale : Algebra.FormallyEtale (RatFunc ℂ) (KummerField n f) :=
  Algebra.FormallyEtale.of_isSeparable _ _

/-- **R01c-1**: `Ω[K⁄ℂ]` is free of rank one on `dx`. -/
noncomputable def kummerKaehlerBasis :
    Module.Basis Unit (KummerField n f) Ω[KummerField n f⁄ℂ] :=
  kaehlerBasisOfEtale ℂ (RatFunc ℂ) (KummerField n f) ratFuncKaehlerBasis

@[simp] lemma kummerKaehlerBasis_apply (i : Unit) :
    kummerKaehlerBasis n f i = KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  rw [kummerKaehlerBasis, kaehlerBasisOfEtale_apply, ratFuncKaehlerBasis_apply,
    KaehlerDifferential.map_D, kummerX_eq]

theorem kummer_kaehler_span_eq_top :
    Submodule.span (KummerField n f)
      {KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f)} = ⊤ := by
  have hrange : Set.range (kummerKaehlerBasis n f) =
      {KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f)} := by
    rw [Set.range_unique, kummerKaehlerBasis_apply]
  rw [← hrange]
  exact (kummerKaehlerBasis n f).span_eq

theorem kummer_D_x_ne_zero : KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) ≠ 0 := by
  have := (kummerKaehlerBasis n f).ne_zero (default : Unit)
  rwa [kummerKaehlerBasis_apply] at this

theorem kummer_kaehler_finrank :
    Module.finrank (KummerField n f) Ω[KummerField n f⁄ℂ] = 1 := by
  rw [Module.finrank_eq_card_basis (kummerKaehlerBasis n f), Fintype.card_unit]

/-- Every differential is a multiple of `dx`. -/
theorem kummer_exists_smul_D_x (ω : Ω[KummerField n f⁄ℂ]) :
    ∃ c : KummerField n f, ω = c • KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  have hmem : ω ∈ Submodule.span (KummerField n f)
      {KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f)} := by
    rw [kummer_kaehler_span_eq_top]; trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨c, hc.symm⟩

/-- The chain rule along `ℂ[x] → K`. -/
theorem kummer_D_algebraMap (p : ℂ[X]) :
    KaehlerDifferential.D ℂ (KummerField n f) (algebraMap ℂ[X] (KummerField n f) p) =
      algebraMap ℂ[X] (KummerField n f) p.derivative •
        KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  have hae : ∀ q : ℂ[X], aeval (kummerX n f) q = algebraMap ℂ[X] (KummerField n f) q := by
    intro q
    rw [kummerX, aeval_algebraMap_apply, aeval_X_left_apply]
  rw [← hae p, (KaehlerDifferential.D ℂ (KummerField n f)).map_aeval p (kummerX n f), hae]

/-- **R01c-1**: `yⁿ = f(x)` differentiates to `n·yⁿ⁻¹·dy = f'(x)·dx`. -/
theorem kummer_D_root :
    ((n : KummerField n f) * AdjoinRoot.root (kummerRat n f) ^ (n - 1)) •
        KaehlerDifferential.D ℂ (KummerField n f) (AdjoinRoot.root (kummerRat n f)) =
      algebraMap ℂ[X] (KummerField n f) f.derivative •
        KaehlerDifferential.D ℂ (KummerField n f) (kummerX n f) := by
  have hpow := (KaehlerDifferential.D ℂ (KummerField n f)).leibniz_pow
    (a := AdjoinRoot.root (kummerRat n f)) n
  rw [kummerRoot_pow, kummer_D_algebraMap] at hpow
  rw [hpow, ← smul_smul, ← Nat.cast_smul_eq_nsmul (KummerField n f)]

end Field

section Quartic

/-- The quartic's branch polynomial `2 − x⁴`: `X⁴ + Y⁴ = 2` is `Y⁴ = 2 − X⁴`. -/
noncomputable def fermatQuartic : ℂ[X] := C 2 - X ^ 4

/-- The nested Fermat polynomial of degree four is the Kummer polynomial of `2 − x⁴`. -/
lemma fermatNested_eq_kummerPoly : fermatNested 4 = kummerPoly 4 fermatQuartic := by
  simp only [fermatNested, kummerPoly, fermatQuartic, map_sub]
  ring

instance fermatQuartic_kummerRat_irreducible : Fact (Irreducible (kummerRat 4 fermatQuartic)) :=
  ⟨by
    rw [← kummerPoly_map]
    refine (kummerPoly_monic 4 fermatQuartic (by norm_num)).irreducible_iff_irreducible_map_fraction_map.mp
      ?_
    rw [← fermatNested_eq_kummerPoly]
    exact fermatNested_irreducible (by norm_num)⟩

end Quartic

#print axioms kummerPoly_irreducible
#print axioms kummerRat_irreducible
#print axioms kummerRingMap_injective
#print axioms kummer_kaehler_finrank
#print axioms kummer_D_root
#print axioms fermatQuartic_kummerRat_irreducible

end CurveSymmetry
