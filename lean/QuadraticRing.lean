import QuadraticDedekind

/-!
# The affine double-cover ring and its maximal ideals (G07b-2b)

`QuadRing h = ℂ[t][W]/(W² − h)`. For squarefree `h` it maps injectively onto the
integral closure of `ℂ[t]` in `ℂ(t)[W]/(W² − h)` (G07b-1). Its maximal ideals are
exactly the kernels of the evaluations `t ↦ c`, `W ↦ d` at the points with
`d² = h(c)`, and distinct points give distinct maximal ideals.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

/-- `W² − h` over `ℂ[t]`. -/
noncomputable def quadPoly (h : ℂ[X]) : (ℂ[X])[X] := X ^ 2 - C h

/-- The affine coordinate ring `ℂ[t][W]/(W² − h)` of the double cover. -/
abbrev QuadRing (h : ℂ[X]) : Type := AdjoinRoot (quadPoly h)

section

variable (h : ℂ[X])

lemma quadPoly_monic : (quadPoly h).Monic := monic_X_pow_sub_C _ two_ne_zero

lemma eval₂_quadPoly {S : Type*} [CommRing S] (i : ℂ[X] →+* S) (x : S) :
    (quadPoly h).eval₂ i x = x ^ 2 - i h := by
  simp [quadPoly]

instance quadRing_isIntegral : Algebra.IsIntegral ℂ[X] (QuadRing h) :=
  haveI := (AdjoinRoot.powerBasis' (quadPoly_monic h)).finite
  Algebra.IsIntegral.of_finite ℂ[X] (QuadRing h)

/-- The comparison map to the field, `W ↦ w`. -/
noncomputable def quadRingMap : QuadRing h →ₐ[ℂ[X]] QuadField h :=
  AdjoinRoot.liftAlgHom (quadPoly h) (Algebra.ofId ℂ[X] (QuadField h))
    (AdjoinRoot.root (quadRat h)) (by
    rw [eval₂_quadPoly, sub_eq_zero, quadRoot_sq]
    exact (IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) h).symm)

lemma quadRingMap_root : quadRingMap h (AdjoinRoot.root (quadPoly h)) =
    AdjoinRoot.root (quadRat h) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- `1` and `w` are independent over `ℂ(t)` when `h ≠ 0`. -/
lemma quad_coeff_eq_zero (hh : h ≠ 0) {a b : RatFunc ℂ}
    (hab : algebraMap (RatFunc ℂ) (QuadField h) a +
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h) = 0) :
    a = 0 ∧ b = 0 := by
  have hc := congrArg (quadConj h) hab
  rw [quadConj_apply, map_zero] at hc
  have h2 : algebraMap (RatFunc ℂ) (QuadField h) (2 * a) = 0 := by
    rw [map_mul, map_ofNat]
    linear_combination hab + hc
  have ha : a = 0 := by
    have := (algebraMap (RatFunc ℂ) (QuadField h)).injective (h2.trans (map_zero _).symm)
    simpa using this
  refine ⟨ha, ?_⟩
  rw [ha, map_zero, zero_add] at hab
  have hb2 : algebraMap (RatFunc ℂ) (QuadField h) (b * algebraMap ℂ[X] (RatFunc ℂ) h) = 0 := by
    rw [map_mul, ← quadRoot_sq]
    linear_combination AdjoinRoot.root (quadRat h) * hab
  have hb3 := (algebraMap (RatFunc ℂ) (QuadField h)).injective (hb2.trans (map_zero _).symm)
  exact (mul_eq_zero.mp hb3).resolve_right (RatFunc.algebraMap_ne_zero hh)

lemma quadRing_exists_eq (x : QuadRing h) :
    ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadRing h) a +
      algebraMap ℂ[X] (QuadRing h) b * AdjoinRoot.root (quadPoly h) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hmon := quadPoly_monic h
    have hne1 : quadPoly h ≠ 1 := by
      intro h1
      have hd : (quadPoly h).natDegree = 2 := natDegree_X_pow_sub_C
      rw [h1, natDegree_one] at hd
      omega
    have hle : (p %ₘ quadPoly h).natDegree ≤ 1 := by
      have hlt := natDegree_modByMonic_lt p hmon hne1
      rw [show (quadPoly h).natDegree = 2 from natDegree_X_pow_sub_C] at hlt
      omega
    have hmk : AdjoinRoot.mk (quadPoly h) p = AdjoinRoot.mk (quadPoly h) (p %ₘ quadPoly h) := by
      rw [AdjoinRoot.mk_eq_mk]
      have hdiv := modByMonic_add_div p (quadPoly h)
      exact ⟨p /ₘ quadPoly h, by linear_combination -hdiv⟩
    refine ⟨(p %ₘ quadPoly h).coeff 0, (p %ₘ quadPoly h).coeff 1, ?_⟩
    rw [hmk]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hle]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rw [← AdjoinRoot.algebraMap_eq]
    ring

lemma quadRingMap_apply (a b : ℂ[X]) :
    quadRingMap h (algebraMap ℂ[X] (QuadRing h) a +
      algebraMap ℂ[X] (QuadRing h) b * AdjoinRoot.root (quadPoly h)) =
    algebraMap ℂ[X] (QuadField h) a +
      algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadRingMap_root]

lemma quadRingMap_injective (hh : h ≠ 0) : Function.Injective (quadRingMap h) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h x
  rw [quadRingMap_apply,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) a,
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) b] at hx
  obtain ⟨ha, hb⟩ := quad_coeff_eq_zero h hh hx
  rw [RatFunc.algebraMap_injective ℂ (ha.trans (map_zero _).symm),
    RatFunc.algebraMap_injective ℂ (hb.trans (map_zero _).symm)]
  simp

/-- G07b-2b (image): for squarefree `h`, `quadRingMap` is injective with image the
integral closure of `ℂ[t]`. -/
theorem quadRingMap_range (hsq : Squarefree h) (x : QuadField h) :
    IsIntegral ℂ[X] x ↔ ∃ y : QuadRing h, quadRingMap h y = x := by
  rw [quad_isIntegral_iff h hsq]
  constructor
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, quadRingMap_apply h a b⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
    exact ⟨a, b, quadRingMap_apply h a b⟩

/-- Evaluation at a point `(c, d)` of the double cover. -/
noncomputable def quadEval (c d : ℂ) (hd : d ^ 2 = h.eval c) : QuadRing h →+* ℂ :=
  AdjoinRoot.lift (evalRingHom c) d (by
    rw [eval₂_quadPoly, coe_evalRingHom, hd, sub_self])

lemma quadEval_of (c d : ℂ) (hd : d ^ 2 = h.eval c) (p : ℂ[X]) :
    quadEval h c d hd (AdjoinRoot.of _ p) = p.eval c :=
  AdjoinRoot.lift_of _

lemma quadEval_root (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    quadEval h c d hd (AdjoinRoot.root _) = d :=
  AdjoinRoot.lift_root _

lemma quadEval_surjective (c d : ℂ) (hd : d ^ 2 = h.eval c) :
    Function.Surjective (quadEval h c d hd) :=
  fun z => ⟨AdjoinRoot.of _ (C z), by rw [quadEval_of, eval_C]⟩

/-- A maximal ideal of `ℂ[t]` contains some `t − c`. -/
lemma exists_X_sub_C_mem {𝔫 : Ideal ℂ[X]} (hmax : 𝔫.IsMaximal) : ∃ c : ℂ, X - C c ∈ 𝔫 := by
  have hbot : ⊥ < 𝔫 := Ideal.bot_lt_of_maximal 𝔫 (Polynomial.not_isField ℂ)
  obtain ⟨p, hp, hp0⟩ := SetLike.exists_of_lt hbot
  have hp0' : p ≠ 0 := by simpa using hp0
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hd : p.degree = 0
    · exfalso
      have hu : IsUnit p := by
        rw [eq_C_of_degree_eq_zero hd]
        exact (isUnit_iff_ne_zero.mpr (by
          intro h0
          apply hp0'
          rw [eq_C_of_degree_eq_zero hd, h0, map_zero])).map C
      exact hmax.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
    · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p hd
      have hfac := mul_divByMonic_eq_iff_isRoot.mpr hr
      rw [← hfac] at hp
      rcases hmax.isPrime.mem_or_mem hp with h1 | h2
      · exact ⟨r, h1⟩
      · have hq0 : p /ₘ (X - C r) ≠ 0 := by
          intro hz
          apply hp0'
          rw [← hfac, hz, mul_zero]
        have hpos : 0 < p.natDegree :=
          Nat.pos_of_ne_zero fun h0 => hd (by rw [degree_eq_natDegree hp0', h0]; rfl)
        have hdeg : (p /ₘ (X - C r)).natDegree < n := by
          rw [natDegree_divByMonic _ (monic_X_sub_C r), natDegree_X_sub_C]
          omega
        exact ih _ hdeg _ h2 (by simpa using hq0) hq0 rfl

/-- G07b-2b: the maximal ideals of `ℂ[t][W]/(W² − h)` are exactly the evaluation
kernels at points `(c, d)` with `d² = h(c)`. -/
theorem quadRing_isMaximal_iff (𝔪 : Ideal (QuadRing h)) :
    𝔪.IsMaximal ↔ ∃ (c d : ℂ) (hd : d ^ 2 = h.eval c), 𝔪 = RingHom.ker (quadEval h c d hd) := by
  constructor
  · intro hmax
    have hcomap := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℂ[X]) 𝔪
    obtain ⟨c, hc⟩ := exists_X_sub_C_mem hcomap
    obtain ⟨d₀, hd₀⟩ := IsAlgClosed.exists_pow_nat_eq (h.eval c) two_pos
    letI : Field (QuadRing h ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let q := Ideal.Quotient.mk 𝔪
    let ι := algebraMap ℂ (QuadRing h ⧸ 𝔪)
    have hqX : q (AdjoinRoot.of _ X) = ι c := by
      have hmem : AdjoinRoot.of (quadPoly h) (X - C c) ∈ 𝔪 := hc
      have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      rw [map_sub, map_sub, sub_eq_zero] at h0
      rw [h0]
      rfl
    have hqp (p : ℂ[X]) : q (AdjoinRoot.of _ p) = ι (p.eval c) := by
      induction p using Polynomial.induction_on' with
      | add p r hp hr => rw [map_add, map_add, hp, hr, eval_add, map_add]
      | monomial n a =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow, hqX, eval_mul,
            eval_C, eval_pow, eval_X, map_mul, map_pow]
          rfl
    have hroot : (q (AdjoinRoot.root _) - ι d₀) * (q (AdjoinRoot.root _) + ι d₀) = 0 := by
      have hsq : AdjoinRoot.root (quadPoly h) ^ 2 = AdjoinRoot.of _ h := by
        have h0 := AdjoinRoot.eval₂_root (quadPoly h)
        rw [eval₂_quadPoly, sub_eq_zero] at h0
        exact h0
      have := congrArg q hsq
      rw [map_pow, hqp, ← hd₀, map_pow] at this
      linear_combination this
    obtain ⟨d, hdd, hqr⟩ : ∃ d : ℂ, d ^ 2 = h.eval c ∧ q (AdjoinRoot.root _) = ι d := by
      rcases mul_eq_zero.mp hroot with h1 | h1
      · exact ⟨d₀, hd₀, sub_eq_zero.mp h1⟩
      · exact ⟨-d₀, by rw [neg_sq, hd₀], by rw [map_neg]; exact eq_neg_of_add_eq_zero_left h1⟩
    refine ⟨c, d, hdd, ?_⟩
    have hext : q = ι.comp (quadEval h c d hdd) := by
      apply AdjoinRoot.ringHom_ext
      · ext p
        · simp only [RingHom.comp_apply]
          rw [hqp, quadEval_of]
        · simp only [RingHom.comp_apply]
          rw [hqp, quadEval_of]
      · simp only [RingHom.comp_apply]
        rw [hqr, quadEval_root]
    have hker := congrArg RingHom.ker hext
    rw [Ideal.mk_ker, RingHom.ker_comp_of_injective _ ι.injective] at hker
    exact hker
  · rintro ⟨c, d, hd, rfl⟩
    exact RingHom.ker_isMaximal_of_surjective _ (quadEval_surjective h c d hd)

/-- Distinct points give distinct maximal ideals. -/
theorem quadEval_ker_injective {c d c' d' : ℂ} (hd : d ^ 2 = h.eval c) (hd' : d' ^ 2 = h.eval c')
    (he : RingHom.ker (quadEval h c d hd) = RingHom.ker (quadEval h c' d' hd')) :
    c = c' ∧ d = d' := by
  have hX : AdjoinRoot.of (quadPoly h) (X - C c) ∈ RingHom.ker (quadEval h c d hd) := by
    rw [RingHom.mem_ker, quadEval_of, eval_sub, eval_X, eval_C, sub_self]
  have hW : AdjoinRoot.root (quadPoly h) - AdjoinRoot.of _ (C d) ∈
      RingHom.ker (quadEval h c d hd) := by
    rw [RingHom.mem_ker, map_sub, quadEval_root, quadEval_of, eval_C, sub_self]
  rw [he, RingHom.mem_ker, quadEval_of, eval_sub, eval_X, eval_C, sub_eq_zero] at hX
  rw [he, RingHom.mem_ker, map_sub, quadEval_root, quadEval_of, eval_C, sub_eq_zero] at hW
  exact ⟨hX.symm, hW.symm⟩

end

/-- G07b-2b for the family: maximal ideals of `ℂ[t][W]/(W² − h_α)` are the points
`(c, d)` with `d² = h_α(c)`, and the ring embeds onto the integral closure of
`ℂ[t]` in the function field of `V_α`. -/
theorem family_quadRing_points {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Function.Injective (quadRingMap (familyH m α)) ∧
      (∀ x : QuadField (familyH m α),
        IsIntegral ℂ[X] x ↔ ∃ y, quadRingMap (familyH m α) y = x) ∧
      ∀ 𝔪 : Ideal (QuadRing (familyH m α)), 𝔪.IsMaximal ↔
        ∃ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c),
          𝔪 = RingHom.ker (quadEval (familyH m α) c d hd) :=
  ⟨quadRingMap_injective _ (familyH_squarefree_of hm ha).ne_zero,
    quadRingMap_range _ (familyH_squarefree_of hm ha),
    quadRing_isMaximal_iff _⟩

#print axioms quadRingMap_injective
#print axioms quadRing_isMaximal_iff
#print axioms quadEval_ker_injective
#print axioms family_quadRing_points

end CurveSymmetry
