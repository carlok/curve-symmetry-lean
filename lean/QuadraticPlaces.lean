import QuadraticRing
import DedekindPlaces

/-!
# Places of the double cover over the finite `t`-line (G07b-2c)

A place of `L = ℂ(t)[W]/(W² − h)` here is a valuation subring `O ≠ L`. Those
containing `ℂ[t]` correspond bijectively to the points `(c, d)` with
`d² = h(c)`: each is the localization of `ℂ[t][W]/(W² − h)` at the evaluation
kernel. Over `t = c` there are two places when `h(c) ≠ 0` and one when
`h(c) = 0`. The place over `t = ∞` is G07b-3.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section

variable (h : ℂ[X])

noncomputable instance quadRingAlgebra : Algebra (QuadRing h) (QuadField h) :=
  (quadRingMap h).toRingHom.toAlgebra

instance quadRing_scalarTower : IsScalarTower ℂ[X] (QuadRing h) (QuadField h) :=
  IsScalarTower.of_algebraMap_eq fun p => ((quadRingMap h).commutes p).symm

lemma algebraMap_quadRing_apply (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y = quadRingMap h y := rfl

/-- The maximal ideal of a point is nonzero: it contains `t − c`. -/
lemma quadEval_ker_ne_bot (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    RingHom.ker (quadEval h c d hd) ≠ ⊥ := by
  intro hb
  have hmem : AdjoinRoot.of (quadPoly h) (X - C c) ∈ RingHom.ker (quadEval h c d hd) := by
    rw [RingHom.mem_ker, quadEval_of, eval_sub, eval_X, eval_C, sub_self]
  rw [hb, Ideal.mem_bot] at hmem
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero (f := quadPoly h) (by
    rw [degree_eq_natDegree (quadPoly_monic h).ne_zero,
      show (quadPoly h).natDegree = 2 from natDegree_X_pow_sub_C]
    decide)
  exact X_sub_C_ne_zero c (hinj (hmem.trans (map_zero _).symm))

instance quadEval_ker_isPrime (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    (RingHom.ker (quadEval h c d hd)).IsPrime :=
  RingHom.ker_isPrime _

/-- The points over `t = c`: two when `h(c) ≠ 0`, one when `h(c) = 0`. -/
theorem quad_points_over (c : ℂ) :
    (h.eval c ≠ 0 → ∃ d₀ : ℂ, d₀ ≠ -d₀ ∧ ∀ d : ℂ, d ^ 2 = h.eval c ↔ d = d₀ ∨ d = -d₀) ∧
      (h.eval c = 0 → ∀ d : ℂ, d ^ 2 = h.eval c ↔ d = 0) := by
  refine ⟨fun hc => ?_, fun hc d => ?_⟩
  · obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq (h.eval c) two_pos
    have h0 : d₀ ≠ 0 := by
      rintro rfl
      exact hc (by simpa using hd₀.symm)
    refine ⟨d₀, fun hn => h0 (by linear_combination hn / 2), fun d => ?_⟩
    rw [← hd₀, sq_eq_sq_iff_eq_or_eq_neg]
  · rw [hc, pow_eq_zero_iff two_ne_zero]

variable [hsq : Fact (Squarefree h)] [hirr : Fact (Irreducible (quadRat h))]

omit hsq in
/-- A valuation subring containing `ℂ[t]` contains `ℂ[t][w]`: `w² = h(t)`. -/
lemma quadRing_mem_of_polynomial_mem (O : ValuationSubring (QuadField h))
    (hO : ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ O) (y : QuadRing h) :
    algebraMap (QuadRing h) (QuadField h) y ∈ O := by
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
  have hw : AdjoinRoot.root (quadRat h) ∈ O := by
    have hsq2 : AdjoinRoot.root (quadRat h) ^ 2 ∈ O := by
      rw [quadRoot_sq, ← IsScalarTower.algebraMap_apply]
      exact hO h
    rcases O.mem_or_inv_mem (AdjoinRoot.root (quadRat h)) with hr | hr
    · exact hr
    · by_cases h0 : AdjoinRoot.root (quadRat h) = 0
      · rw [h0]
        exact O.zero_mem
      · have he : AdjoinRoot.root (quadRat h) =
            AdjoinRoot.root (quadRat h) ^ 2 * (AdjoinRoot.root (quadRat h))⁻¹ := by
          field_simp
        rw [he]
        exact mul_mem hsq2 hr
  rw [algebraMap_quadRing_apply, quadRingMap_apply]
  exact add_mem (hO a) (mul_mem (hO b) hw)

instance quadRing_isDomain : IsDomain (QuadRing h) :=
  Function.Injective.isDomain (quadRingMap h).toRingHom
    (quadRingMap_injective h hsq.out.ne_zero)

instance quadRing_isIntegralClosure : IsIntegralClosure (QuadRing h) ℂ[X] (QuadField h) where
  algebraMap_injective := quadRingMap_injective h hsq.out.ne_zero
  isIntegral_iff {x} := quadRingMap_range h hsq.out x

instance quadRing_isDedekindDomain : IsDedekindDomain (QuadRing h) :=
  IsIntegralClosure.isDedekindDomain ℂ[X] (RatFunc ℂ) (QuadField h) (QuadRing h)

instance quadRing_isFractionRing : IsFractionRing (QuadRing h) (QuadField h) :=
  IsIntegralClosure.isFractionRing_of_finite_extension ℂ[X] (RatFunc ℂ) (QuadField h) (QuadRing h)

/-- The place of `L` at the point `(c, d)` of the affine double cover. -/
noncomputable def quadPlace (c d : ℂ) (hd : d ^ 2 = h.eval c) : ValuationSubring (QuadField h) :=
  primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
    (quadEval_ker_ne_bot h c d hd)

/-- G07b-2c: places of `L` containing `ℂ[t]` are exactly the point places, and
distinct points give distinct places. -/
theorem quad_finite_place_classification :
    (∀ (c d : ℂ) (hd : d ^ 2 = h.eval c), quadPlace h c d hd ≠ ⊤ ∧
        ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ quadPlace h c d hd) ∧
      (∀ O : ValuationSubring (QuadField h), O ≠ ⊤ →
        (∀ p : ℂ[X], algebraMap ℂ[X] (QuadField h) p ∈ O) →
          ∃ (c d : ℂ) (hd : d ^ 2 = h.eval c), O = quadPlace h c d hd) ∧
      (∀ (c d c' d' : ℂ) (hd : d ^ 2 = h.eval c) (hd' : d' ^ 2 = h.eval c'),
        quadPlace h c d hd = quadPlace h c' d' hd' → c = c' ∧ d = d') := by
  refine ⟨fun c d hd => ⟨primeValuationSubring_ne_top _ _, fun p => ?_⟩, fun O htop hO => ?_,
    fun c d c' d' hd hd' he => ?_⟩
  · rw [IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
    exact algebraMap_mem_primeValuationSubring _ _
  · have hA := quadRing_mem_of_polynomial_mem h O hO
    have hO' := eq_primeValuationSubring_placeCenter O hA htop
    have hmax : (placeCenter (QuadField h) O hA).IsMaximal :=
      (inferInstance : (placeCenter (QuadField h) O hA).IsPrime).isMaximal
        (placeCenter_ne_bot O hA htop)
    obtain ⟨c, d, hd, hP⟩ := (quadRing_isMaximal_iff h _).mp hmax
    refine ⟨c, d, hd, hO'.trans ?_⟩
    exact primeValuationSubring_congr _ _ hP
  · exact quadEval_ker_injective h hd hd' (primeValuationSubring_injective _ _ he)

end

instance familyH_squarefree_fact {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)] :
    Fact (Squarefree (familyH m α)) :=
  ⟨familyH_squarefree_of hm.out ha.out⟩

/-- G07b-2c for the family: the places of the function field of `V_α` containing
`ℂ[t]` are the point places `(c, d)`, `d² = h_α(c)`, bijectively. -/
theorem family_finite_place_classification {m : ℕ} {α : ℂ} [Fact (0 < m)]
    [Fact (α ≠ star α)] :
    (∀ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), quadPlace (familyH m α) c d hd ≠ ⊤ ∧
        ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m α)) p ∈
          quadPlace (familyH m α) c d hd) ∧
      (∀ O : ValuationSubring (QuadField (familyH m α)), O ≠ ⊤ →
        (∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m α)) p ∈ O) →
          ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∧
      (∀ (c d c' d' : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
        (hd' : d' ^ 2 = (familyH m α).eval c'),
        quadPlace (familyH m α) c d hd = quadPlace (familyH m α) c' d' hd' → c = c' ∧ d = d') :=
  quad_finite_place_classification (familyH m α)

#print axioms quad_finite_place_classification
#print axioms quad_points_over
#print axioms family_finite_place_classification

end CurveSymmetry
