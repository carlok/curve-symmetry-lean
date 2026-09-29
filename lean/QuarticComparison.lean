import FermatHolomorphic
import FamilyGenus
import PaperBounds
import Sharpness

/-!
# The quartic is not similar to an `m = 2` family curve (R01f)

Remark 5 of the note: `Re(z⁴) = 1` attains the rotation bound in degree four but
is not in the `m = 2` family, because the genera are three and two. This module
proves the non-similarity through genus:

* a direct similarity `S(z) = az + b` carrying one real locus onto another makes
  the two defining polynomials associates after the substitution `S`
  (`similarity_span_eq`): `dvd_of_realLocus_subset` applies in both directions,
  so no degree bookkeeping is needed. The substitution is an automorphism of
  `ℂ[X, Y]` (`simPullEquiv`), so the coordinate rings, hence the function fields,
  are isomorphic as `ℂ`-algebras (`similarityFunctionFieldEquiv`);
* the function field of `X⁴ + Y⁴ = 2` is the Kummer field of R01c-1
  (`fermatFunctionFieldAlgEquiv`, through `kummerRing_isFractionRing`);
* genus is invariant (R01a); the family's is `2` (R01b); the quartic has three
  independent holomorphic differentials (R01d), so its genus is not `2`
  (`quartic_three_le_genus`).

`quartic_not_similar_family` and `quartic_not_oppositeSimilar_family` state the
result for both kinds of similarity; the opposite case reduces to the direct
one because the quartic is symmetric under conjugation. That the quartic's genus
is exactly three is R01e.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section KummerFraction

variable (n : ℕ) (f : ℂ[X])

noncomputable instance kummerRing_algebra : Algebra (KummerRing n f) (KummerField n f) :=
  (kummerRingMap n f).toRingHom.toAlgebra

lemma kummerRing_algebraMap_apply (r : KummerRing n f) :
    algebraMap (KummerRing n f) (KummerField n f) r = kummerRingMap n f r :=
  rfl

instance kummerRing_scalarTower : IsScalarTower ℂ (KummerRing n f) (KummerField n f) :=
  IsScalarTower.of_algebraMap_eq fun z => by
    rw [kummerRing_algebraMap_apply, IsScalarTower.algebraMap_apply ℂ ℂ[X] (KummerRing n f),
      AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

/-- The Kummer field is the fraction field of the Kummer ring: clearing the denominators of
the coefficients writes every element as a quotient. -/
theorem kummerRing_isFractionRing (hn : n ≠ 0) [Fact (Irreducible (kummerRat n f))] :
    IsFractionRing (KummerRing n f) (KummerField n f) := by
  have : FaithfulSMul (KummerRing n f) (KummerField n f) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (kummerRingMap_injective n f hn)
  refine IsFractionRing.of_field (R := KummerRing n f) (K := KummerField n f) fun z => ?_
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨b, hb, hbp⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors ℂ[X]) p
  have hb0 : algebraMap ℂ[X] (KummerField n f) b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (KummerField n f)]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (KummerField n f)).injective).mpr
      (RatFunc.algebraMap_ne_zero (nonZeroDivisors.ne_zero hb))
  refine ⟨AdjoinRoot.mk _ (IsLocalization.integerNormalization (nonZeroDivisors ℂ[X]) p),
    algebraMap ℂ[X] (KummerRing n f) b, ?_⟩
  rw [kummerRing_algebraMap_apply, kummerRing_algebraMap_apply, kummerRingMap_mk, hbp,
    AlgHom.commutes, eq_div_iff hb0, Algebra.smul_def, map_mul, Polynomial.algebraMap_apply,
    AdjoinRoot.mk_C, mul_comm]
  congr 1

end KummerFraction

section Fermat

/-- The coordinate ring `ℂ[X, Y]/(X^d + Y^d − 2)` of the Fermat curve. -/
abbrev FermatCoordinateRing (d : ℕ) : Type := BPoly ⧸ Ideal.span {fermatPolynomial d}

/-- The function field of the Fermat curve `X^d + Y^d = 2`. -/
abbrev FermatFunctionField (d : ℕ) : Type := FractionRing (FermatCoordinateRing d)

instance fermatCoordinateRing_isDomain (d : ℕ) [NeZero d] : IsDomain (FermatCoordinateRing d) := by
  have : (Ideal.span {fermatPolynomial d}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime
      (UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (fermat_irreducible (Nat.pos_of_ne_zero (NeZero.ne d))))
  exact Ideal.Quotient.isDomain _

/-- `ℂ[X, Y]/(X⁴ + Y⁴ − 2) ≅ ℂ[x][Y]/(Y⁴ − (2 − x⁴))`, through `toNested`. -/
noncomputable def fermatCoordinateRingEquiv :
    FermatCoordinateRing 4 ≃ₐ[ℂ] KummerRing 4 fermatQuartic :=
  Ideal.quotientEquivAlg (Ideal.span {fermatPolynomial 4})
    (Ideal.span {kummerPoly 4 fermatQuartic}) toNested (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      exact ((fermat_toNested 4).trans fermatNested_eq_kummerPoly).symm)

/-- **R01f**: the function field of `X⁴ + Y⁴ = 2` is the Kummer field of `y⁴ = 2 − x⁴`. -/
noncomputable def fermatFunctionFieldAlgEquiv :
    FermatFunctionField 4 ≃ₐ[ℂ] KummerField 4 fermatQuartic :=
  haveI := kummerRing_isFractionRing 4 fermatQuartic (by norm_num)
  IsFractionRing.algEquivOfAlgEquiv fermatCoordinateRingEquiv

end Fermat

section Similarity

/-- The pullback along the direct similarity `z ↦ az + b`, in the coordinates `X = z`,
`Y = z̄`. -/
noncomputable def simPull (a b : ℂ) : BPoly →ₐ[ℂ] BPoly :=
  MvPolynomial.aeval fun i : Fin 2 =>
    if i = 0 then MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b
    else MvPolynomial.C (star a) * MvPolynomial.X 1 + MvPolynomial.C (star b)

lemma eval_simPull (a b z : ℂ) (P : BPoly) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (simPull a b P) =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a * z + b else star (a * z + b)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [simPull]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, map_mul, map_mul, hP]
      congr 1
      fin_cases i <;> simp [simPull, star_add, star_mul, mul_comm]

lemma mem_realLocus_simPull (a b z : ℂ) (P : BPoly) :
    z ∈ realLocus (simPull a b P) ↔ a * z + b ∈ realLocus P := by
  change MvPolynomial.eval _ (simPull a b P) = 0 ↔ _
  rw [eval_simPull]
  rfl

lemma simPull_comp (a b a' b' : ℂ) :
    (simPull a b).comp (simPull a' b') = simPull (a' * a) (a' * b + b') := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [simPull, star_mul, star_add] <;> ring

lemma simPull_one_zero : simPull 1 0 = AlgHom.id ℂ BPoly := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [simPull]

/-- The pullback along a similarity is an automorphism, with the inverse similarity's
pullback as inverse. -/
noncomputable def simPullEquiv (a b : ℂ) (ha : a ≠ 0) : BPoly ≃ₐ[ℂ] BPoly :=
  AlgEquiv.ofAlgHom (simPull a b) (simPull a⁻¹ (-(a⁻¹ * b)))
    (by rw [simPull_comp, inv_mul_cancel₀ ha, show a⁻¹ * b + -(a⁻¹ * b) = 0 by ring,
      simPull_one_zero])
    (by rw [simPull_comp, mul_inv_cancel₀ ha,
      show a * -(a⁻¹ * b) + b = 0 by field_simp; ring, simPull_one_zero])

lemma simPullEquiv_symm_apply (a b : ℂ) (ha : a ≠ 0) (P : BPoly) :
    (simPullEquiv a b ha).symm P = simPull a⁻¹ (-(a⁻¹ * b)) P :=
  rfl

/-- **R01f**: if a direct similarity carries the real locus of `Q` onto that of `P`, both
irreducible with infinite real loci, then `P` and the substituted `Q` generate the same ideal. -/
theorem similarity_span_eq {P Q : BPoly} (hP : Irreducible P) (hQ : Irreducible Q)
    (hPinf : (realLocus P).Infinite) (hQinf : (realLocus Q).Infinite) {a b : ℂ} (ha : a ≠ 0)
    (h : (fun z : ℂ => a * z + b) '' realLocus Q = realLocus P) :
    Ideal.span {P} =
      (Ideal.span {Q}).map ((simPullEquiv a b ha).symm : BPoly →+* BPoly) := by
  have h1 : Q ∣ simPull a b P := dvd_of_realLocus_subset hQ hQinf fun z hz => by
    rw [mem_realLocus_simPull, ← h]
    exact ⟨z, hz, rfl⟩
  have h2 : P ∣ simPull a⁻¹ (-(a⁻¹ * b)) Q := dvd_of_realLocus_subset hP hPinf fun w hw => by
    rw [← h] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    rw [mem_realLocus_simPull]
    convert hz using 1
    field_simp
    ring
  have h3 : simPull a⁻¹ (-(a⁻¹ * b)) Q ∣ P := by
    have hmap := map_dvd (simPull a⁻¹ (-(a⁻¹ * b))) h1
    rwa [← AlgHom.comp_apply, simPull_comp, mul_inv_cancel₀ ha,
      show a * -(a⁻¹ * b) + b = 0 by field_simp; ring, simPull_one_zero,
      AlgHom.id_apply] at hmap
  rw [Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton.mpr (associated_of_dvd_dvd h2 h3)]
  rfl

/-- **R01f**: a direct similarity between the real loci of two irreducible equations with
infinite real loci gives an isomorphism of `ℂ`-algebras between their function fields. -/
noncomputable def similarityFunctionFieldEquiv {P Q : BPoly} (hP : Irreducible P)
    (hQ : Irreducible Q) (hPinf : (realLocus P).Infinite) (hQinf : (realLocus Q).Infinite)
    {a b : ℂ} (ha : a ≠ 0) (h : (fun z : ℂ => a * z + b) '' realLocus Q = realLocus P) :
    FractionRing (BPoly ⧸ Ideal.span {Q}) ≃ₐ[ℂ] FractionRing (BPoly ⧸ Ideal.span {P}) :=
  IsFractionRing.algEquivOfAlgEquiv
    (Ideal.quotientEquivAlg (Ideal.span {Q}) (Ideal.span {P}) (simPullEquiv a b ha).symm
      (similarity_span_eq hP hQ hPinf hQinf ha h))

end Similarity

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic

/-- The real locus of `X⁴ + Y⁴ − 2` is the curve `Re(z⁴) = 1`. -/
lemma realLocus_fermat_four : realLocus (fermatPolynomial 4) = {z : ℂ | (z ^ 4).re = 1} := by
  ext z
  change MvPolynomial.eval _ (fermatPolynomial 4) = 0 ↔ _
  rw [eval_fermat, show star (z ^ 4) = (starRingEnd ℂ) (z ^ 4) from rfl, Complex.add_conj]
  change _ ↔ (z ^ 4).re = 1
  constructor
  · intro h0
    push_cast at h0
    have : (((z ^ 4).re : ℝ) : ℂ) = 1 := by linear_combination h0 / 2
    exact_mod_cast this
  · intro h1
    rw [h1]
    norm_num

/-- The quartic `Re(z⁴) = 1` is symmetric under conjugation. -/
lemma image_star_quartic (a b : ℂ) :
    (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} =
      (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} := by
  have hstar : star '' {z : ℂ | (z ^ 4).re = 1} = {z : ℂ | (z ^ 4).re = 1} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [← map_pow, Complex.conj_re] using hz
    · intro hw
      exact ⟨star w, by simpa [← map_pow, Complex.conj_re] using hw, star_star w⟩
  calc (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1}
      = (fun z : ℂ => a * z + b) '' (star '' {z : ℂ | (z ^ 4).re = 1}) := by
        rw [Set.image_image]
    _ = (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} := by rw [hstar]

/-- With finitely many holomorphic differentials, the quartic has at least three. -/
theorem quartic_three_le_genus [Module.Finite ℂ (holomorphicSpace K₄)] : 3 ≤ genus K₄ := by
  have hli : LinearIndependent ℂ
      (fun i : Fin 3 => (⟨quarticHolo i, quarticHolo_mem i⟩ : holomorphicSpace K₄)) :=
    LinearIndependent.of_comp (holomorphicSpace K₄).subtype quarticHolo_linearIndependent
  rw [genus]
  simpa using hli.fintype_card_le_finrank

/-- **R01f**: no direct similarity carries `Re(z⁴) = 1` onto an `m = 2` family curve. -/
theorem quartic_not_similar_family {α : ℂ} (hα : α ≠ star α) {a b : ℂ} (ha : a ≠ 0) :
    (fun z : ℂ => a * z + b) '' {z : ℂ | (z ^ 4).re = 1} ≠ extremalCurve 2 α := by
  intro hS
  have hm : Fact (0 < 2) := ⟨by norm_num⟩
  have hα' : Fact (α ≠ star α) := ⟨hα⟩
  rw [← realLocus_fermat_four, ← family_locus_eq] at hS
  let e : FermatFunctionField 4 ≃ₐ[ℂ] FamilyFunctionField 2 α :=
    similarityFunctionFieldEquiv (familyPolynomial_irreducible (by norm_num) hα)
      (fermat_irreducible (by norm_num)) (family_realLocus_infinite (by norm_num) hα)
      (fermat_realLocus_infinite (by norm_num)) ha hS
  have hg : genus K₄ = 2 :=
    (genus_congr (fermatFunctionFieldAlgEquiv.symm.trans e)).trans familyFunctionField_genus
  have hpos : 0 < Module.finrank ℂ (holomorphicSpace K₄) := by
    rw [show Module.finrank ℂ (holomorphicSpace K₄) = genus K₄ from rfl, hg]
    norm_num
  have hfin : Module.Finite ℂ (holomorphicSpace K₄) := Module.finite_of_finrank_pos hpos
  have := quartic_three_le_genus
  omega

/-- **R01f**: nor does an orientation-reversing similarity `z ↦ a·z̄ + b`. -/
theorem quartic_not_oppositeSimilar_family {α : ℂ} (hα : α ≠ star α) {a b : ℂ} (ha : a ≠ 0) :
    (fun z : ℂ => a * star z + b) '' {z : ℂ | (z ^ 4).re = 1} ≠ extremalCurve 2 α := by
  rw [image_star_quartic]
  exact quartic_not_similar_family hα ha

end Quartic

#print axioms kummerRing_isFractionRing
#print axioms fermatFunctionFieldAlgEquiv
#print axioms similarity_span_eq
#print axioms quartic_not_similar_family
#print axioms quartic_not_oppositeSimilar_family

end CurveSymmetry
