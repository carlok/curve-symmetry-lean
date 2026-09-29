import KummerField
import FunctionFieldGenus

/-!
# Three holomorphic differentials on the quartic (R01d)

The quartic `X⁴ + Y⁴ = 2` has function field `K = ℂ(x)[y]/(y⁴ − (2 − x⁴))`
(R01c-1), where `x⁴ + y⁴ = 2` and `y³·dy = −x³·dx`. The three differentials

    dx/y³,   x·dx/y³,   y·dx/y³ = dx/y²

are regular at every place of `K` in the sense of R01a (`quarticHolo_mem`) and
linearly independent over `ℂ` (`quarticHolo_linearIndependent`), so the
holomorphic differentials of `K` have dimension at least three. They are the
canonical differentials of a smooth plane quartic.

No classification of the places is needed. At a place `O` containing `ℂ`:

* if `x, 1/y ∈ O`, the coefficient against `dx` lies in `O`;
* if `x ∈ O` but `1/y ∉ O`, then `y ∈ O` (from `y⁴ = 2 − x⁴`), and `x` is a unit,
  since `x⁴ + y⁴ = 2` is a unit of `O` and `y⁴` is not; `dx = −(y³/x³)·dy` then
  gives a coefficient in `O` against `dy`;
* if `x ∉ O`, then `s = 1/x ∈ O`, `r = y/x ∈ O` with `r⁴ = 2s⁴ − 1` a unit, and
  `dx = −x²·ds` gives a coefficient in `O` against `ds`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section ValuationRing

variable {K : Type*} [Field K] (O : ValuationSubring K)

/-- In a valuation subring, `aⁿ ∈ O` with `n ≠ 0` forces `a ∈ O`. -/
lemma valuationSubring_mem_of_pow_mem {a : K} {n : ℕ} (hn : n ≠ 0) (h : a ^ n ∈ O) :
    a ∈ O := by
  by_contra ha
  have hinv : a⁻¹ ∈ O := (O.mem_or_inv_mem a).resolve_left ha
  have ha0 : a ≠ 0 := fun h0 => ha (h0 ▸ O.zero_mem)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  have hk : a ^ (k + 1) * a⁻¹ ^ k = a := by
    rw [pow_succ', mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0, one_pow, mul_one]
  exact ha (hk ▸ mul_mem h (pow_mem hinv k))

/-- For `a ∈ O`, being a unit of `O` means `a⁻¹ ∈ O`. -/
lemma valuationSubring_isUnit_iff {a : K} (ha : a ∈ O) (ha0 : a ≠ 0) :
    IsUnit (⟨a, ha⟩ : O) ↔ a⁻¹ ∈ O := by
  constructor
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hab : a * (b : K) = 1 := congrArg Subtype.val hb
    rw [inv_eq_of_mul_eq_one_right hab]
    exact b.2
  · intro h
    exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, h⟩, Subtype.ext (mul_inv_cancel₀ ha0),
      Subtype.ext (inv_mul_cancel₀ ha0)⟩, rfl⟩

end ValuationRing

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic

instance quarticField_charZero : CharZero K₄ :=
  charZero_of_injective_algebraMap (algebraMap ℂ K₄).injective

/-- The coordinate `x` of the quartic's function field. -/
noncomputable abbrev quarticX : K₄ := kummerX 4 fermatQuartic

/-- The coordinate `y` of the quartic's function field. -/
noncomputable abbrev quarticY : K₄ := AdjoinRoot.root (kummerRat 4 fermatQuartic)

lemma quartic_polynomial_injective : Function.Injective (algebraMap ℂ[X] K₄) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) K₄]
  exact (algebraMap (RatFunc ℂ) K₄).injective.comp (IsFractionRing.injective ℂ[X] (RatFunc ℂ))

lemma quarticY_pow : quarticY ^ 4 = 2 - quarticX ^ 4 := by
  rw [quarticY, kummerRoot_pow]
  show algebraMap ℂ[X] K₄ (C 2 - X ^ 4) = 2 - quarticX ^ 4
  rw [map_sub, map_pow, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄,
    map_ofNat]
  rfl

/-- The quartic's equation `x⁴ + y⁴ = 2`. -/
lemma quartic_relation : quarticX ^ 4 + quarticY ^ 4 = 2 := by
  rw [quarticY_pow]
  ring

lemma quarticX_ne_zero : quarticX ≠ 0 := by
  intro h0
  have : algebraMap ℂ[X] K₄ X = algebraMap ℂ[X] K₄ 0 := by
    rw [map_zero]
    exact h0
  exact X_ne_zero (quartic_polynomial_injective this)

lemma quarticY_ne_zero : quarticY ≠ 0 := by
  intro h0
  have h := kummerRoot_pow 4 fermatQuartic
  rw [show AdjoinRoot.root (kummerRat 4 fermatQuartic) = quarticY from rfl, h0,
    zero_pow (by norm_num)] at h
  have hf : (C 2 - X ^ 4 : ℂ[X]) = 0 := quartic_polynomial_injective (by rw [map_zero]; exact h.symm)
  have := congrArg (eval 0) hf
  simp at this

/-- `x⁴ + y⁴ = 2` differentiates to `y³·dy = −x³·dx`. -/
lemma quartic_D_relation :
    quarticY ^ 3 • KaehlerDifferential.D ℂ K₄ quarticY =
      (-(quarticX ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticX := by
  have h := kummer_D_root 4 fermatQuartic
  have hder : algebraMap ℂ[X] K₄ (derivative fermatQuartic) = -(4 * quarticX ^ 3) := by
    show algebraMap ℂ[X] K₄ (derivative (C 2 - X ^ 4)) = -(4 * quarticX ^ 3)
    have h4C : (algebraMap ℂ[X] K₄) (C (4 : ℂ)) = 4 := by
      rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄, map_ofNat]
    rw [derivative_sub, derivative_C, zero_sub, derivative_X_pow, map_neg, map_mul, map_pow]
    simp only [Nat.cast_ofNat, h4C]
    rfl
  rw [hder, show (4 - 1 : ℕ) = 3 from rfl] at h
  have h4 : (4 : K₄) ≠ 0 := by norm_num
  calc quarticY ^ 3 • KaehlerDifferential.D ℂ K₄ quarticY
      = ((4 : K₄)⁻¹ * ((4 : ℕ) * quarticY ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticY := by
        rw [Nat.cast_ofNat, ← mul_assoc, inv_mul_cancel₀ h4, one_mul]
    _ = (4 : K₄)⁻¹ • (-(4 * quarticX ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticX := by
        rw [← smul_smul, h]
    _ = (-(quarticX ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticX := by
        rw [smul_smul]
        congr 1
        field_simp

/-- `dx = −x²·d(1/x)`. -/
lemma quartic_D_x_inv :
    KaehlerDifferential.D ℂ K₄ quarticX =
      (-(quarticX ^ 2)) • KaehlerDifferential.D ℂ K₄ quarticX⁻¹ := by
  rw [Derivation.leibniz_inv, smul_smul]
  have hx := quarticX_ne_zero
  rw [show -(quarticX ^ 2) * -(quarticX⁻¹ ^ 2) = 1 by field_simp, one_smul]

/-- **R01d, criterion**: `F·dx` is holomorphic once its coefficient passes three local tests,
one for each kind of place. -/
theorem quartic_smul_dx_mem_holomorphicSpace (F : K₄)
    (h1 : ∀ O : ValuationSubring K₄,
      quarticX ∈ O → quarticY ∈ O → quarticY⁻¹ ∈ O → F ∈ O)
    (h2 : ∀ O : ValuationSubring K₄, quarticX ∈ O → quarticX⁻¹ ∈ O → quarticY ∈ O →
      F * quarticY ^ 3 * quarticX⁻¹ ^ 3 ∈ O)
    (h3 : ∀ O : ValuationSubring K₄, quarticX⁻¹ ∈ O → quarticX * quarticY⁻¹ ∈ O →
      F * quarticX ^ 2 ∈ O) :
    F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ := by
  rw [mem_holomorphicSpace]
  intro O hO
  have hx0 := quarticX_ne_zero
  have hy0 := quarticY_ne_zero
  have htwo : (2 : K₄) ∈ O := by
    have := hO.2 2
    rwa [map_ofNat] at this
  have htwoinv : (2 : K₄)⁻¹ ∈ O := by
    have := hO.2 2⁻¹
    rwa [map_inv₀, map_ofNat] at this
  have htwo_unit : IsUnit (⟨2, htwo⟩ : O) :=
    (valuationSubring_isUnit_iff O htwo (by norm_num)).mpr htwoinv
  by_cases hx : quarticX ∈ O
  · have hy : quarticY ∈ O := valuationSubring_mem_of_pow_mem O (n := 4) (by norm_num)
      (by rw [quarticY_pow]; exact sub_mem htwo (pow_mem hx 4))
    by_cases hyi : quarticY⁻¹ ∈ O
    · exact smul_D_mem_regularAt (h1 O hx hy hyi) hx
    · -- `x` is a unit: `x⁴ + y⁴ = 2` is one and `y⁴` is not
      have hsum : (⟨quarticX, hx⟩ : O) ^ 4 + (⟨quarticY, hy⟩ : O) ^ 4 = ⟨2, htwo⟩ :=
        Subtype.ext quartic_relation
      have hxi : quarticX⁻¹ ∈ O := by
        rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hsum ▸ htwo_unit) with hX | hY
        · exact (valuationSubring_isUnit_iff O hx hx0).mp ((isUnit_pow_iff (by norm_num)).mp hX)
        · exact absurd ((valuationSubring_isUnit_iff O hy hy0).mp
            ((isUnit_pow_iff (by norm_num)).mp hY)) hyi
      have hdx : KaehlerDifferential.D ℂ K₄ quarticX =
          (-(quarticY ^ 3 * quarticX⁻¹ ^ 3)) • KaehlerDifferential.D ℂ K₄ quarticY := by
        have hrel := congrArg (fun ω => (-(quarticX⁻¹ ^ 3)) • ω) quartic_D_relation
        simp only [smul_smul] at hrel
        rw [show -(quarticX⁻¹ ^ 3) * -(quarticX ^ 3) = 1 by field_simp, one_smul] at hrel
        rw [← hrel]
        congr 1
        ring
      rw [hdx, smul_smul]
      refine smul_D_mem_regularAt ?_ hy
      rw [show F * -(quarticY ^ 3 * quarticX⁻¹ ^ 3) = -(F * quarticY ^ 3 * quarticX⁻¹ ^ 3) by
        ring]
      exact neg_mem (h2 O hx hxi hy)
  · have hxi : quarticX⁻¹ ∈ O := (O.mem_or_inv_mem _).resolve_left hx
    have hr4 : (quarticY * quarticX⁻¹) ^ 4 = 2 * quarticX⁻¹ ^ 4 - 1 := by
      rw [mul_pow, quarticY_pow]
      field_simp
    have hr : quarticY * quarticX⁻¹ ∈ O := valuationSubring_mem_of_pow_mem O (n := 4) (by norm_num)
      (by rw [hr4]; exact sub_mem (mul_mem htwo (pow_mem hxi 4)) (one_mem O))
    have hr0 : quarticY * quarticX⁻¹ ≠ 0 := mul_ne_zero hy0 (inv_ne_zero hx0)
    -- `r = y/x` is a unit: `r⁴ − 2s⁴ = −1` and `s = 1/x` is not a unit
    have hrunit : IsUnit (⟨_, hr⟩ : O) := by
      have hsum : (⟨_, hr⟩ : O) ^ 4 + -(⟨2, htwo⟩ * (⟨quarticX⁻¹, hxi⟩ : O) ^ 4) = -1 :=
        Subtype.ext (by
          change (quarticY * quarticX⁻¹) ^ 4 + -(2 * quarticX⁻¹ ^ 4) = -1
          rw [hr4]
          ring)
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hsum ▸ isUnit_one.neg) with hR | hS
      · exact (isUnit_pow_iff (by norm_num)).mp hR
      · exfalso
        have hS4 : IsUnit ((⟨quarticX⁻¹, hxi⟩ : O) ^ 4) :=
          isUnit_of_mul_isUnit_right (IsUnit.neg_iff _ |>.mp hS)
        have := (valuationSubring_isUnit_iff O hxi (inv_ne_zero hx0)).mp
          ((isUnit_pow_iff (by norm_num)).mp hS4)
        rw [inv_inv] at this
        exact hx this
    have hrinv : quarticX * quarticY⁻¹ ∈ O := by
      have := (valuationSubring_isUnit_iff O hr hr0).mp hrunit
      rwa [mul_inv, inv_inv, mul_comm] at this
    rw [quartic_D_x_inv, smul_smul]
    refine smul_D_mem_regularAt ?_ hxi
    rw [show F * -(quarticX ^ 2) = -(F * quarticX ^ 2) by ring]
    exact neg_mem (h3 O hxi hrinv)

/-- The numerators `1, x, y` of the canonical differentials `P·dx/y³`. -/
noncomputable def quarticHoloNum : Fin 3 → K₄ := ![1, quarticX, quarticY]

/-- The differentials `dx/y³`, `x·dx/y³` and `y·dx/y³ = dx/y²`. -/
noncomputable def quarticHolo (i : Fin 3) : Ω[K₄⁄ℂ] :=
  (quarticHoloNum i * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX

/-- Holomorphy of `P·dx/y³` from the membership of the numerator `P` at the places. -/
lemma quartic_num_mem {P : K₄}
    (hP1 : ∀ O : ValuationSubring K₄, quarticX ∈ O → quarticY ∈ O → P ∈ O)
    (hP3 : ∀ O : ValuationSubring K₄, quarticX⁻¹ ∈ O → quarticX * quarticY⁻¹ ∈ O →
      P * quarticY⁻¹ ^ 3 * quarticX ^ 2 ∈ O) :
    (P * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ := by
  have hx0 := quarticX_ne_zero
  have hy0 := quarticY_ne_zero
  apply quartic_smul_dx_mem_holomorphicSpace
  · intro O hx hy hyi
    exact mul_mem (hP1 O hx hy) (pow_mem hyi 3)
  · intro O hx hxi hy
    rw [show P * quarticY⁻¹ ^ 3 * quarticY ^ 3 * quarticX⁻¹ ^ 3 = P * quarticX⁻¹ ^ 3 by
      field_simp]
    exact mul_mem (hP1 O hx hy) (pow_mem hxi 3)
  · exact hP3

/-- **R01d**: `dx/y³`, `x·dx/y³` and `dx/y²` are holomorphic. -/
theorem quarticHolo_mem (i : Fin 3) : quarticHolo i ∈ holomorphicSpace K₄ := by
  have hx0 := quarticX_ne_zero
  have hy0 := quarticY_ne_zero
  fin_cases i
  · show ((1 : K₄) * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ _
    refine quartic_num_mem (fun O _ _ => one_mem O) fun O hxi hr => ?_
    rw [show (1 : K₄) * quarticY⁻¹ ^ 3 * quarticX ^ 2 =
      quarticX⁻¹ * (quarticX * quarticY⁻¹) ^ 3 by field_simp]
    exact mul_mem hxi (pow_mem hr 3)
  · show (quarticX * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ _
    refine quartic_num_mem (fun O hx _ => hx) fun O _ hr => ?_
    rw [show quarticX * quarticY⁻¹ ^ 3 * quarticX ^ 2 = (quarticX * quarticY⁻¹) ^ 3 by
      field_simp]
    exact pow_mem hr 3
  · show (quarticY * quarticY⁻¹ ^ 3) • KaehlerDifferential.D ℂ K₄ quarticX ∈ _
    refine quartic_num_mem (fun O _ hy => hy) fun O _ hr => ?_
    rw [show quarticY * quarticY⁻¹ ^ 3 * quarticX ^ 2 = (quarticX * quarticY⁻¹) ^ 2 by
      field_simp]
    exact pow_mem hr 2

/-- `a + b·x + c·y = 0` in the quartic's function field forces `a = b = c = 0`: the
minimal polynomial of `y` over `ℂ(x)` has degree four. -/
lemma quartic_lin_eq_zero {a b c : ℂ}
    (h : algebraMap ℂ K₄ a + algebraMap ℂ K₄ b * quarticX + algebraMap ℂ K₄ c * quarticY = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  set A : RatFunc ℂ := algebraMap ℂ[X] (RatFunc ℂ) (C a + C b * X) with hAdef
  set B : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) c with hBdef
  have hmk : AdjoinRoot.mk (kummerRat 4 fermatQuartic) (C A + C B * X) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, ← h]
    rw [hAdef, hBdef, ← AdjoinRoot.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) K₄,
      ← IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) K₄, map_add, map_mul]
    simp only [quarticX, kummerX, quarticY]
    rw [C_eq_algebraMap, C_eq_algebraMap, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄,
      ← IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄]
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hdeg : (C A + C B * X).natDegree < (kummerRat 4 fermatQuartic).natDegree := by
    rw [show (kummerRat 4 fermatQuartic).natDegree = 4 from natDegree_X_pow_sub_C]
    have := natDegree_linear_le (a := B) (b := A)
    rw [add_comm] at this
    omega
  have hzero := eq_zero_of_dvd_of_natDegree_lt hmk hdeg
  have hA : A = 0 := by simpa using congrArg (coeff · 0) hzero
  have hB : B = 0 := by simpa using congrArg (coeff · 1) hzero
  have hpoly : (C a + C b * X : ℂ[X]) = 0 :=
    IsFractionRing.injective ℂ[X] (RatFunc ℂ) (hA.trans (map_zero _).symm)
  have ha : a = 0 := by simpa using congrArg (coeff · 0) hpoly
  have hb : b = 0 := by simpa using congrArg (coeff · 1) hpoly
  have hc : c = 0 := (algebraMap ℂ (RatFunc ℂ)).injective (hB.trans (map_zero _).symm)
  exact ⟨ha, hb, hc⟩

/-- **R01d**: the three differentials are linearly independent over `ℂ`, so the holomorphic
differentials of the quartic have dimension at least three. -/
theorem quarticHolo_linearIndependent : LinearIndependent ℂ quarticHolo := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsum : ∑ i, g i • quarticHolo i =
      ((algebraMap ℂ K₄ (g 0) + algebraMap ℂ K₄ (g 1) * quarticX +
          algebraMap ℂ K₄ (g 2) * quarticY) * quarticY⁻¹ ^ 3) •
        KaehlerDifferential.D ℂ K₄ quarticX := by
    simp only [Fin.sum_univ_three, quarticHolo, quarticHoloNum, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [← algebraMap_smul K₄ (g 0), ← algebraMap_smul K₄ (g 1), ← algebraMap_smul K₄ (g 2),
      smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul]
    congr 1
    ring
  rw [hsum] at hg
  have hcoef := (smul_eq_zero.mp hg).resolve_right (kummer_D_x_ne_zero 4 fermatQuartic)
  have hlin : algebraMap ℂ K₄ (g 0) + algebraMap ℂ K₄ (g 1) * quarticX +
      algebraMap ℂ K₄ (g 2) * quarticY = 0 :=
    (mul_eq_zero.mp hcoef).resolve_right (pow_ne_zero 3 (inv_ne_zero quarticY_ne_zero))
  obtain ⟨h0, h1, h2⟩ := quartic_lin_eq_zero hlin
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

end Quartic

#print axioms quartic_smul_dx_mem_holomorphicSpace
#print axioms quarticHolo_mem
#print axioms quarticHolo_linearIndependent

end CurveSymmetry
