import KummerPlaces

/-!
# The quartic's chart at infinity (R01e-1)

For `X⁴ + Y⁴ = 2`, written `y⁴ = f(x)` with `f = 2 − x⁴`, the substitution
`x = 1/s`, `y = r/s` turns the equation into `r⁴ = 2s⁴ − 1 = g(s)`. So the
function field `K = KummerField 4 f` is isomorphic, as a `ℂ`-algebra, to
`K' = KummerField 4 g` (`fermatInfinityAlgEquiv`), with `x ↦ 1/s` and
`y ↦ r/s`. Both `f` and `g` are squarefree of degree four, so R01c-2 applies to
both fields.

The places of `K` not containing `x` correspond to the points of `K'` over
`s = 0`: `r⁴ = −1`, four unramified points. The genus computation needs one
of them: `fermatInfinityPlace`, the pull-back of the place of `K'` at `(0, ζ)`
with `ζ⁴ = −1`. There `s` is a uniformizer and `r` a unit, and a differential
`F·dx` of `K` is regular exactly when `φ(F)/s²` lies in the local ring
(`fermat_regularAt_infinity_iff`), since `d(1/s) = −ds/s²`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

/-- `2s⁴ − 1`: the quartic's equation in the chart at infinity is `r⁴ = 2s⁴ − 1`. -/
noncomputable def fermatDual : ℂ[X] := C 2 * X ^ 4 - 1

lemma fermatQuartic_squarefree : Squarefree fermatQuartic := by
  have hsep : (X ^ 4 - C (2 : ℂ)).Separable :=
    separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  have hassoc : Associated (X ^ 4 - C (2 : ℂ)) fermatQuartic :=
    ⟨-1, by simp only [Units.val_neg, Units.val_one, fermatQuartic]; ring⟩
  exact hassoc.squarefree_iff.mp hsep.squarefree

lemma fermatDual_squarefree : Squarefree fermatDual := by
  have hsep : (X ^ 4 - C (1 / 2 : ℂ)).Separable :=
    separable_X_pow_sub_C _ (by norm_num) (by norm_num)
  have h2 : IsUnit (C (2 : ℂ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr two_ne_zero)
  have hassoc : Associated (X ^ 4 - C (1 / 2 : ℂ)) fermatDual := by
    refine ⟨h2.unit, ?_⟩
    rw [IsUnit.unit_spec, fermatDual, sub_mul, ← C_mul, show (1 / 2 : ℂ) * 2 = 1 by norm_num, C_1]
    ring
  exact hassoc.squarefree_iff.mp hsep.squarefree

lemma fermatQuartic_natDegree : fermatQuartic.natDegree = 4 := by
  unfold fermatQuartic
  compute_degree!

lemma fermatDual_natDegree : fermatDual.natDegree = 4 := by
  unfold fermatDual
  compute_degree!

instance fermatQuartic_squarefree_fact : Fact (Squarefree fermatQuartic) :=
  ⟨fermatQuartic_squarefree⟩

instance fermatQuartic_natDegree_fact : Fact (0 < fermatQuartic.natDegree) :=
  ⟨by rw [fermatQuartic_natDegree]; norm_num⟩

instance fermatDual_squarefree_fact : Fact (Squarefree fermatDual) :=
  ⟨fermatDual_squarefree⟩

instance fermatDual_natDegree_fact : Fact (0 < fermatDual.natDegree) :=
  ⟨by rw [fermatDual_natDegree]; norm_num⟩

local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual

/-- The chart coordinate `s` of `K'`. -/
noncomputable abbrev dualS : K₄' := kummerX 4 fermatDual

/-- The chart coordinate `r` of `K'`. -/
noncomputable abbrev dualR : K₄' := AdjoinRoot.root (kummerRat 4 fermatDual)

lemma dualS_eq : dualS = algebraMap (RatFunc ℂ) K₄' RatFunc.X := kummerX_eq 4 fermatDual

lemma dualS_ne_zero : dualS ≠ 0 := by
  rw [dualS_eq]
  exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) K₄').injective).mpr RatFunc.X_ne_zero

lemma dualR_pow : dualR ^ 4 = 2 * dualS ^ 4 - 1 := by
  rw [dualR, kummerRoot_pow]
  show algebraMap ℂ[X] K₄' (C 2 * X ^ 4 - 1) = _
  rw [map_sub, map_mul, map_pow, map_one, C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄', map_ofNat]
  rfl

/-- `f(1/s) = 2 − 1/s⁴` in `ℂ(s)`. -/
lemma fermatQuartic_ratInv :
    ratInv (algebraMap ℂ[X] (RatFunc ℂ) fermatQuartic) =
      2 - ((RatFunc.X : RatFunc ℂ)⁻¹) ^ 4 := by
  rw [ratInv_algebraMap]
  show aeval (RatFunc.X : RatFunc ℂ)⁻¹ (C 2 - X ^ 4) = _
  rw [map_sub, aeval_C, map_pow, aeval_X, map_ofNat]

/-- The chart map `x ↦ 1/s`, `y ↦ r/s`. -/
noncomputable def fermatInfinityMap : K₄ →+* K₄' :=
  AdjoinRoot.lift ((algebraMap (RatFunc ℂ) K₄').comp ratInv.toRingHom)
    (dualR * dualS⁻¹) (by
      have hs := dualS_ne_zero
      show eval₂ _ _ (X ^ 4 - C (algebraMap ℂ[X] (RatFunc ℂ) fermatQuartic)) = 0
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.comp_apply,
        AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, fermatQuartic_ratInv, map_sub, map_pow,
        map_inv₀, ← dualS_eq, map_ofNat, mul_pow, dualR_pow]
      field_simp
      ring)

lemma fermatInfinityMap_of (q : RatFunc ℂ) :
    fermatInfinityMap (algebraMap (RatFunc ℂ) K₄ q) = algebraMap (RatFunc ℂ) K₄' (ratInv q) :=
  AdjoinRoot.lift_of _

lemma fermatInfinityMap_root :
    fermatInfinityMap (AdjoinRoot.root (kummerRat 4 fermatQuartic)) = dualR * dualS⁻¹ :=
  AdjoinRoot.lift_root _

lemma fermatInfinityMap_x : fermatInfinityMap quarticX = dualS⁻¹ := by
  rw [quarticX, kummerX_eq, fermatInfinityMap_of, ratInv_X, map_inv₀, ← dualS_eq]

lemma fermatInfinityMap_surjective : Function.Surjective fermatInfinityMap := by
  let φ := fermatInfinityMap
  have hadd {a b : K₄'} (ha : a ∈ Set.range φ) (hb : b ∈ Set.range φ) : a + b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add φ x y⟩
  have hmul {a b : K₄'} (ha : a ∈ Set.range φ) (hb : b ∈ Set.range φ) : a * b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x * y, map_mul φ x y⟩
  have hof (q : RatFunc ℂ) : algebraMap (RatFunc ℂ) K₄' q ∈ Set.range φ := by
    obtain ⟨p, rfl⟩ := ratInv_surjective q
    exact ⟨algebraMap (RatFunc ℂ) K₄ p, fermatInfinityMap_of p⟩
  have hroot : dualR ∈ Set.range φ := by
    have he : dualR = φ (AdjoinRoot.root (kummerRat 4 fermatQuartic)) * dualS := by
      rw [fermatInfinityMap_root, mul_assoc, inv_mul_cancel₀ dualS_ne_zero, mul_one]
    rw [he, dualS_eq]
    exact hmul ⟨_, rfl⟩ (hof _)
  intro z
  induction z using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a =>
        rw [AdjoinRoot.mk_C]
        exact hof a
    | add p q hp hq =>
        rw [map_add]
        exact hadd hp hq
    | monomial k a hk =>
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
        exact hmul hk hroot

lemma fermatInfinityMap_bijective : Function.Bijective fermatInfinityMap :=
  ⟨fermatInfinityMap.injective, fermatInfinityMap_surjective⟩

/-- **R01e-1**: the chart isomorphism `x ↦ 1/s`, `y ↦ r/s`, as `ℂ`-algebras. -/
noncomputable def fermatInfinityAlgEquiv : K₄ ≃ₐ[ℂ] K₄' :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective fermatInfinityMap fermatInfinityMap_bijective)
    fun z => by
      rw [RingEquiv.ofBijective_apply, IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) K₄,
        fermatInfinityMap_of, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

@[simp] lemma fermatInfinityAlgEquiv_apply (z : K₄) :
    fermatInfinityAlgEquiv z = fermatInfinityMap z :=
  rfl

/-- A fourth root of `−1`: the four places over `s = 0` are the points `(0, ζ)`, `ζ⁴ = −1`. -/
noncomputable def fermatZeta : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by norm_num : 0 < 4)).choose

lemma fermatZeta_pow : fermatZeta ^ 4 = fermatDual.eval 0 := by
  rw [fermatZeta, (IsAlgClosed.exists_pow_nat_eq (-1 : ℂ) (by norm_num : 0 < 4)).choose_spec]
  simp [fermatDual]

lemma fermatDual_eval_zero : fermatDual.eval 0 ≠ 0 := by
  simp [fermatDual]

/-- The local ring of `K'` at `(0, ζ)`. -/
noncomputable abbrev dualLocalRing : Subalgebra (KummerRing 4 fermatDual) K₄' :=
  kummerLocalRing 0 fermatZeta fermatZeta_pow

/-- **R01e-1**: a place of the quartic's function field over `x = ∞`. -/
noncomputable def fermatInfinityPlace : ValuationSubring K₄ :=
  (kummerPlace (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow).comap
    (fermatInfinityAlgEquiv : K₄ →+* K₄')

lemma fermatInfinityPlace_isComplexPlace : IsComplexPlace fermatInfinityPlace :=
  (kummerPlace_isComplexPlace (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow).comap _

/-- **R01e-1**: `F·dx` is regular at the place at infinity exactly when `φ(F)/s²` lies in the
local ring at `(0, ζ)`, because `x = 1/s` and `d(1/s) = −ds/s²`. -/
theorem fermat_regularAt_infinity_iff (F : K₄) :
    F • KaehlerDifferential.D ℂ K₄ quarticX ∈ regularAt fermatInfinityPlace ↔
      fermatInfinityMap F * (dualS⁻¹) ^ 2 ∈ dualLocalRing := by
  rw [fermatInfinityPlace, mem_regularAt_comap_iff, kaehlerTransport_smul, kaehlerTransport_D,
    fermatInfinityAlgEquiv_apply, fermatInfinityAlgEquiv_apply, fermatInfinityMap_x,
    Derivation.leibniz_inv, smul_smul,
    kummer_regularAt_unramified (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow
      fermatDual_eval_zero, mem_kummerPlace_iff, mul_neg]
  exact neg_mem_iff

/-- The chart coordinate `s` lies in the local ring at `(0, ζ)`. -/
lemma dualS_mem : dualS ∈ dualLocalRing := by
  rw [dualS, kummerX]
  exact kummerLocal_poly_mem (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow X

/-- `s` is not a unit there: `1/s` is not in the local ring. -/
lemma dualS_inv_notMem : dualS⁻¹ ∉ dualLocalRing := by
  intro hmem
  set u := algebraMap (KummerRing 4 fermatDual) dualLocalRing (kummerShift 4 fermatDual 0)
  have hmax : u ∈ IsLocalRing.maximalIdeal dualLocalRing :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff dualLocalRing
      (RingHom.ker (kummerEval 4 fermatDual 0 fermatZeta fermatZeta_pow)) _).mpr
      (kummerShift_mem_ker 0 fermatZeta fermatZeta_pow)
  have hu : (u : K₄') = dualS := by
    show algebraMap (KummerRing 4 fermatDual) K₄' (kummerShift 4 fermatDual 0) = _
    rw [kummerShift, ← IsScalarTower.algebraMap_apply, C_0, sub_zero]
    rfl
  have h1 : u * ⟨dualS⁻¹, hmem⟩ = 1 := Subtype.ext (by
    change (u : K₄') * dualS⁻¹ = 1
    rw [hu, mul_inv_cancel₀ dualS_ne_zero])
  have hunit : IsUnit u := ⟨⟨u, ⟨dualS⁻¹, hmem⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit

/-- The place lies over `x = ∞`: `x` is not in it. -/
lemma quarticX_notMem_fermatInfinityPlace : quarticX ∉ fermatInfinityPlace := by
  intro h
  have h' : fermatInfinityMap quarticX ∈ dualLocalRing := h
  rw [fermatInfinityMap_x] at h'
  exact dualS_inv_notMem h'

/-- The chart coordinate `r` is a unit there: `r(0, ζ) = ζ ≠ 0`. -/
lemma dualR_mem_and_inv_mem : dualR ∈ dualLocalRing ∧ dualR⁻¹ ∈ dualLocalRing := by
  refine ⟨kummerLocal_root_mem (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow, ?_⟩
  have hζ : fermatZeta ≠ 0 := by
    intro h0
    have := fermatZeta_pow
    rw [h0, zero_pow (by norm_num)] at this
    exact fermatDual_eval_zero this.symm
  have hmem : AdjoinRoot.root (kummerPoly 4 fermatDual) ∈
      (RingHom.ker (kummerEval 4 fermatDual 0 fermatZeta fermatZeta_pow)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, kummerEval_root]
    exact hζ
  obtain ⟨v, hv⟩ := (IsLocalization.map_units dualLocalRing ⟨_, hmem⟩).exists_right_inv
  have hcoe : dualR * (v : K₄') = 1 := by
    have hc1 := congrArg (fun z : dualLocalRing => (z : K₄')) hv
    simp only [Subalgebra.coe_mul, Subalgebra.coe_one] at hc1
    show AdjoinRoot.root (kummerRat 4 fermatDual) * (v : K₄') = 1
    rw [← kummerRingMap_root]
    exact hc1
  rw [inv_eq_of_mul_eq_one_right hcoe]
  exact v.2

#print axioms fermatInfinityAlgEquiv
#print axioms fermat_regularAt_infinity_iff
#print axioms quarticX_notMem_fermatInfinityPlace
#print axioms dualR_mem_and_inv_mem

end CurveSymmetry
