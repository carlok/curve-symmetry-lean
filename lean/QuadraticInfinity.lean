import QuadraticPlaces

/-!
# The place over `t = ∞` and the full place classification (G07b-3)

With `s = 1/t` and `w' = w·s^(m+1)`, the double cover of the family with
parameter `α` becomes the double cover with parameter `conj α`:
`w'² = h_{conj α}(s)`. `familyInfinityMap` is the resulting ring isomorphism
`ℂ(t)[W]/(W² − h_α) ≃ ℂ(s)[W]/(W² − h_{conj α})`, with `t ↦ 1/s`. Pulling back
the point place `(0, 0)` gives the unique place of the function field of `V_α`
not containing `t`. Every place containing the constants is either a point
place over the finite `t`-line (G07b-2c) or this place.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial
open scoped nonZeroDivisors

section Generic

variable {A K : Type*} [CommRing A] [Field K] [Algebra A K]

/-- An element of the center has no inverse in the valuation subring. -/
lemma inv_notMem_of_mem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    {a : A} (ha : a ∈ placeCenter K O hO) (ha0 : algebraMap A K a ≠ 0) :
    (algebraMap A K a)⁻¹ ∉ O := by
  intro hinv
  rw [mem_placeCenter] at ha
  have h1 := (O.valuation_le_one_iff _).mpr hinv
  rw [map_inv₀] at h1
  have hpos : 0 < O.valuation (algebraMap A K a) := by
    rw [Valuation.pos_iff]
    exact ha0
  exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr ha)

end Generic

/-! ### The involution `t ↦ 1/t` of `ℂ(t)` -/

lemma ratFunc_aeval_X (p : ℂ[X]) :
    aeval (RatFunc.X : RatFunc ℂ) p = algebraMap ℂ[X] (RatFunc ℂ) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | monomial n a =>
      rw [aeval_monomial, ← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_C,
        RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]

lemma ratFunc_X_inv_transcendental : Transcendental ℂ (RatFunc.X : RatFunc ℂ)⁻¹ := by
  have hX : Transcendental ℂ (RatFunc.X : RatFunc ℂ) := by
    rw [transcendental_iff_injective]
    intro p q hpq
    rw [ratFunc_aeval_X, ratFunc_aeval_X] at hpq
    exact RatFunc.algebraMap_injective ℂ hpq
  intro halg
  exact hX (IsAlgebraic.inv_iff.mp halg)

lemma ratInv_hφ : (ℂ[X])⁰ ≤ (RatFunc ℂ)⁰.comap (aeval (R := ℂ) (RatFunc.X : RatFunc ℂ)⁻¹) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (transcendental_iff_injective.mp ratFunc_X_inv_transcendental)

/-- The `ℂ`-algebra endomorphism of `ℂ(t)` sending `t` to `1/t`. -/
noncomputable def ratInv : RatFunc ℂ →ₐ[ℂ] RatFunc ℂ :=
  RatFunc.liftAlgHom (aeval (RatFunc.X : RatFunc ℂ)⁻¹) ratInv_hφ

lemma ratInv_algebraMap (p : ℂ[X]) :
    ratInv (algebraMap ℂ[X] (RatFunc ℂ) p) = aeval (RatFunc.X : RatFunc ℂ)⁻¹ p := by
  have h := RatFunc.liftAlgHom_apply_div (φ := aeval (RatFunc.X : RatFunc ℂ)⁻¹)
    (hφ := ratInv_hφ) p 1
  simp only [map_one, div_one] at h
  exact h

lemma ratInv_X : ratInv (RatFunc.X : RatFunc ℂ) = (RatFunc.X : RatFunc ℂ)⁻¹ := by
  have h := ratInv_algebraMap X
  rwa [aeval_X, RatFunc.algebraMap_X] at h

lemma ratInv_C (c : ℂ) : ratInv (algebraMap ℂ[X] (RatFunc ℂ) (C c)) =
    algebraMap ℂ[X] (RatFunc ℂ) (C c) := by
  rw [ratInv_algebraMap, aeval_C, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]

lemma ratInv_surjective : Function.Surjective ratInv := by
  have hpoly (p : ℂ[X]) : algebraMap ℂ[X] (RatFunc ℂ) p ∈ Set.range ratInv := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
        obtain ⟨a, ha⟩ := hp
        obtain ⟨b, hb⟩ := hq
        exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | monomial n c =>
        refine ⟨algebraMap ℂ[X] (RatFunc ℂ) (C c) * ((RatFunc.X : RatFunc ℂ)⁻¹) ^ n, ?_⟩
        rw [map_mul, ratInv_C, map_pow, map_inv₀, ratInv_X, inv_inv, ← C_mul_X_pow_eq_monomial,
          map_mul, map_pow, RatFunc.algebraMap_X]
  intro f
  obtain ⟨a, ha⟩ := hpoly f.num
  obtain ⟨b, hb⟩ := hpoly f.denom
  exact ⟨a / b, by rw [map_div₀, ha, hb, RatFunc.num_div_denom]⟩

/-- `h_α(1/s) = h_{conj α}(s) · s^(-(2m+2))`. -/
lemma familyH_inv_identity (m : ℕ) (α : ℂ) :
    aeval (RatFunc.X : RatFunc ℂ)⁻¹ (familyH m α) =
      algebraMap ℂ[X] (RatFunc ℂ) (familyH m (star α)) *
        ((RatFunc.X : RatFunc ℂ)⁻¹) ^ (2 * m + 2) := by
  have hX := RatFunc.X_ne_zero (K := ℂ)
  simp only [familyH, familyB, familyA, map_neg, map_mul, map_add, map_pow, aeval_X, aeval_C,
    map_one, RatFunc.algebraMap_X, RatFunc.algebraMap_C, star_star, RatFunc.algebraMap_eq_C,
    inv_pow]
  field_simp
  ring

/-! ### The isomorphism with the chart at infinity -/

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

instance star_ne_star_star_fact : Fact (star α ≠ star (star α)) :=
  ⟨by simpa only [star_star, ne_comm] using ha.out⟩

omit hm in
lemma familyH_eval_zero (m : ℕ) (α : ℂ) : (familyH m α).eval 0 = 0 := by
  simp [familyH, familyB]

variable (m α) in
/-- `t ↦ 1/s`, `w ↦ w'·s^(-(m+1))`. -/
noncomputable def familyInfinityMap :
    QuadField (familyH m α) →+* QuadField (familyH m (star α)) :=
  AdjoinRoot.lift ((algebraMap (RatFunc ℂ) (QuadField (familyH m (star α)))).comp ratInv.toRingHom)
    (AdjoinRoot.root (quadRat (familyH m (star α))) *
      (algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (RatFunc.X : RatFunc ℂ)⁻¹) ^ (m + 1))
    (by
      rw [eval₂_quadRat, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        ratInv_algebraMap, familyH_inv_identity, map_mul, map_pow, mul_pow, quadRoot_sq]
      ring)

lemma familyInfinityMap_of (r : RatFunc ℂ) :
    familyInfinityMap m α (algebraMap (RatFunc ℂ) (QuadField (familyH m α)) r) =
      algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (ratInv r) :=
  AdjoinRoot.lift_of _

lemma familyInfinityMap_root :
    familyInfinityMap m α (AdjoinRoot.root (quadRat (familyH m α))) =
      AdjoinRoot.root (quadRat (familyH m (star α))) *
        (algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (RatFunc.X : RatFunc ℂ)⁻¹) ^
          (m + 1) :=
  AdjoinRoot.lift_root _

lemma familyInfinityMap_surjective : Function.Surjective (familyInfinityMap m α) := by
  let φ := familyInfinityMap m α
  have hadd {a b : QuadField (familyH m (star α))} (ha' : a ∈ Set.range φ) (hb : b ∈ Set.range φ) :
      a + b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add φ x y⟩
  have hmul {a b : QuadField (familyH m (star α))} (ha' : a ∈ Set.range φ) (hb : b ∈ Set.range φ) :
      a * b ∈ Set.range φ := by
    obtain ⟨x, rfl⟩ := ha'
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x * y, map_mul φ x y⟩
  have hof (r : RatFunc ℂ) :
      algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) r ∈ Set.range φ := by
    obtain ⟨q, rfl⟩ := ratInv_surjective r
    exact ⟨algebraMap (RatFunc ℂ) (QuadField (familyH m α)) q, familyInfinityMap_of q⟩
  have hroot : AdjoinRoot.root (quadRat (familyH m (star α))) ∈ Set.range φ := by
    have hX := RatFunc.X_ne_zero (K := ℂ)
    have he : AdjoinRoot.root (quadRat (familyH m (star α))) =
        φ (AdjoinRoot.root (quadRat (familyH m α))) *
          algebraMap (RatFunc ℂ) (QuadField (familyH m (star α))) (RatFunc.X ^ (m + 1)) := by
      rw [familyInfinityMap_root, mul_assoc, map_pow, ← mul_pow, ← map_mul, inv_mul_cancel₀ hX,
        map_one, one_pow, mul_one]
    rw [he]
    exact hmul ⟨_, rfl⟩ (hof _)
  intro y
  induction y using AdjoinRoot.induction_on with
  | ih p =>
    induction p using Polynomial.induction_on with
    | C a =>
        rw [AdjoinRoot.mk_C]
        exact hof a
    | add p q hp hq =>
        rw [map_add]
        exact hadd hp hq
    | monomial n a hn =>
        rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
        exact hmul hn hroot

variable (m α) in
/-- The ring isomorphism with the chart at infinity. -/
noncomputable def familyInfinityEquiv :
    QuadField (familyH m α) ≃+* QuadField (familyH m (star α)) :=
  RingEquiv.ofBijective (familyInfinityMap m α)
    ⟨(familyInfinityMap m α).injective, familyInfinityMap_surjective⟩

lemma familyInfinityMap_polyC (c : ℂ) :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) (C c)) =
      algebraMap ℂ[X] (QuadField (familyH m (star α))) (C c) := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, ratInv_C,
    ← IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α)))]

lemma familyInfinityMap_t :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) X) =
      (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, RatFunc.algebraMap_X, ratInv_X, map_inv₀,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m (star α))),
    RatFunc.algebraMap_X]

omit hm ha in
lemma familyH_star_zero_point (m : ℕ) (α : ℂ) : (0 : ℂ) ^ 2 = (familyH m (star α)).eval 0 := by
  rw [familyH_eval_zero]
  ring

variable (m α) in
/-- The place of the function field of `V_α` over `t = ∞`. -/
noncomputable def familyInfinityPlace : ValuationSubring (QuadField (familyH m α)) :=
  (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).comap
    (familyInfinityMap m α)

lemma mem_familyInfinityPlace (x : QuadField (familyH m α)) :
    x ∈ familyInfinityPlace m α ↔
      familyInfinityMap m α x ∈ quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α) :=
  Iff.rfl

/-- In a point place over `s = c`, the coordinate `s` is invertible iff `c ≠ 0`. -/
lemma quadPlace_X_inv_mem_iff (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
    (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    (algebraMap ℂ[X] (QuadField h) X)⁻¹ ∈ quadPlace h c d hd ↔ c ≠ 0 := by
  have hA := algebraMap_mem_primeValuationSubring (K := QuadField h)
    (quadEval_ker_ne_bot h c d hd)
  have hcenter := placeCenter_primeValuationSubring (K := QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd)
  have hXeq : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.of (quadPoly h) X) =
      algebraMap ℂ[X] (QuadField h) X :=
    ((quadRingMap h).commutes X)
  have hmem : AdjoinRoot.of (quadPoly h) X ∈ RingHom.ker (quadEval h c d hd) ↔ c = 0 := by
    rw [RingHom.mem_ker, quadEval_of, eval_X]
  have hX0 : algebraMap ℂ[X] (QuadField h) X ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h), RatFunc.algebraMap_X]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      RatFunc.X_ne_zero
  change (algebraMap ℂ[X] (QuadField h) X)⁻¹ ∈ primeValuationSubring (QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd) ↔ c ≠ 0
  rw [← hXeq]
  constructor
  · intro hinv hc
    have hin : AdjoinRoot.of (quadPoly h) X ∈ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_notMem_of_mem_placeCenter _ hA hin (hXeq ▸ hX0) hinv
  · intro hc
    have hnot : AdjoinRoot.of (quadPoly h) X ∉ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_mem_of_notMem_placeCenter _ hA hnot

lemma familyInfinityPlace_ne_top : familyInfinityPlace m α ≠ ⊤ := by
  intro htop
  apply ((quad_finite_place_classification (familyH m (star α))).1 0 0
    (familyH_star_zero_point m α)).1
  refine top_unique fun y _ => ?_
  obtain ⟨x, rfl⟩ := familyInfinityMap_surjective (m := m) (α := α) y
  have hx : x ∈ familyInfinityPlace m α := by
    rw [htop]
    exact ValuationSubring.mem_top _
  exact (mem_familyInfinityPlace x).mp hx

lemma familyInfinityPlace_const (c : ℂ) :
    algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace, familyInfinityMap_polyC]
  exact ((quad_finite_place_classification (familyH m (star α))).1 0 0
    (familyH_star_zero_point m α)).2 _

lemma familyInfinityPlace_t_notMem :
    algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ familyInfinityPlace m α := by
  rw [mem_familyInfinityPlace, familyInfinityMap_t]
  intro hmem
  exact ((quadPlace_X_inv_mem_iff _ 0 0 (familyH_star_zero_point m α)).mp hmem) rfl

/-- A place containing the constants and `t` is a point place (G07b-2c). -/
lemma place_eq_quadPlace_of_t_mem (O : ValuationSubring (QuadField (familyH m α)))
    (htop : O ≠ ⊤) (hconst : ∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O)
    (ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O) :
    ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd := by
  apply (quad_finite_place_classification (familyH m α)).2.1 O htop
  intro p
  induction p using Polynomial.induction_on with
  | C a => exact hconst a
  | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
  | monomial n a hn =>
      rw [pow_succ, ← mul_assoc, map_mul]
      exact mul_mem hn ht

lemma familyInfinityEquiv_symm_apply {x : QuadField (familyH m α)}
    {y : QuadField (familyH m (star α))} (hxy : familyInfinityMap m α x = y) :
    (familyInfinityEquiv m α).symm y = x := by
  rw [← hxy]
  exact (familyInfinityEquiv m α).symm_apply_apply x

/-- A place containing the constants but not `t` is the place at infinity. -/
lemma place_eq_infinity_of_t_notMem (O : ValuationSubring (QuadField (familyH m α)))
    (htop : O ≠ ⊤) (hconst : ∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O)
    (ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ O) :
    O = familyInfinityPlace m α := by
  let e := familyInfinityEquiv m α
  let Q := O.comap e.symm.toRingHom
  have hQmem (y : QuadField (familyH m (star α))) : y ∈ Q ↔ e.symm y ∈ O := Iff.rfl
  have hQtop : Q ≠ ⊤ := by
    intro hQ
    apply htop
    refine top_unique fun x _ => ?_
    have hx : e x ∈ Q := by
      rw [hQ]
      exact ValuationSubring.mem_top _
    rwa [hQmem, RingEquiv.symm_apply_apply] at hx
  have htinv : (algebraMap ℂ[X] (QuadField (familyH m α)) X)⁻¹ ∈ O :=
    (O.mem_or_inv_mem _).resolve_left ht
  have hsX : e.symm (algebraMap ℂ[X] (QuadField (familyH m (star α))) X) =
      (algebraMap ℂ[X] (QuadField (familyH m α)) X)⁻¹ := by
    apply familyInfinityEquiv_symm_apply
    rw [map_inv₀, familyInfinityMap_t, inv_inv]
  have hsXinv : e.symm (algebraMap ℂ[X] (QuadField (familyH m (star α))) X)⁻¹ =
      algebraMap ℂ[X] (QuadField (familyH m α)) X :=
    familyInfinityEquiv_symm_apply familyInfinityMap_t
  have hQpoly : ∀ p : ℂ[X], algebraMap ℂ[X] (QuadField (familyH m (star α))) p ∈ Q := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        rw [hQmem, familyInfinityEquiv_symm_apply (familyInfinityMap_polyC a)]
        exact hconst a
    | add p q hp hq =>
        rw [map_add]
        exact add_mem hp hq
    | monomial n a hn =>
        rw [pow_succ, ← mul_assoc, map_mul]
        refine mul_mem hn ?_
        rw [hQmem, hsX]
        exact htinv
  obtain ⟨c, d, hd, hQ⟩ :=
    (quad_finite_place_classification (familyH m (star α))).2.1 Q hQtop hQpoly
  have hc : c = 0 := by
    by_contra hc
    have hin := (quadPlace_X_inv_mem_iff _ c d hd).mpr hc
    rw [← hQ, hQmem, hsXinv] at hin
    exact ht hin
  subst hc
  have hd0 : d = 0 := by
    rw [familyH_eval_zero] at hd
    exact (pow_eq_zero_iff two_ne_zero).mp hd
  subst hd0
  ext x
  rw [mem_familyInfinityPlace]
  change x ∈ O ↔ e x ∈ quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
  rw [← hQ, hQmem, RingEquiv.symm_apply_apply]

/-- G07b-3: the function field of `V_α` has exactly one place containing the
constants but not `t`, and every place containing the constants is a point
place over the finite `t`-line or this place at infinity. -/
theorem family_place_classification :
    (familyInfinityPlace m α ≠ ⊤ ∧
        (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ familyInfinityPlace m α) ∧
        algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ familyInfinityPlace m α) ∧
      ∀ O : ValuationSubring (QuadField (familyH m α)), O ≠ ⊤ →
        (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O) →
          (∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd) ∨
            O = familyInfinityPlace m α := by
  refine ⟨⟨familyInfinityPlace_ne_top, familyInfinityPlace_const, familyInfinityPlace_t_notMem⟩,
    fun O htop hconst => ?_⟩
  by_cases ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O
  · exact Or.inl (place_eq_quadPlace_of_t_mem O htop hconst ht)
  · exact Or.inr (place_eq_infinity_of_t_notMem O htop hconst ht)

#print axioms familyInfinityMap_surjective
#print axioms family_place_classification

end CurveSymmetry
