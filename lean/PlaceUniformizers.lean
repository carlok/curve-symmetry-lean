import PlaceDifferentials

/-!
# A uniformizer at an unramified point place (G09a-2e)

At a point place `(c, d)` of the double cover with `h(c) ≠ 0`, the coordinate
`t − c` generates the maximal ideal of the local ring. Its differential is `dt`,
so `dt` is the differential of a uniformizer there: in the language of G09a-2c,
a differential `f·dt` is regular at such a place exactly when `f` lies in the
local ring, which is the statement `ord_v(dt) = 0` without introducing a
`ℤ`-valued order.

The ramified point places, where `h(c) = 0` and `w` is the uniformizer, and the
place at infinity are not treated here.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

/-- The coordinate `t − c` of the coordinate ring of the double cover. -/
noncomputable def quadShift : QuadRing h := algebraMap ℂ[X] (QuadRing h) (X - C c)

omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadEval_algebraMap (p : ℂ[X]) :
    quadEval h c d hd (algebraMap ℂ[X] (QuadRing h) p) = p.eval c := by
  rw [AdjoinRoot.algebraMap_eq, quadEval_of]

omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadShift_mem_ker : quadShift h c ∈ RingHom.ker (quadEval h c d hd) := by
  rw [RingHom.mem_ker, quadShift, quadEval_algebraMap]
  simp

omit [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))] in
lemma quadRing_root_sq : AdjoinRoot.root (quadPoly h) ^ 2 = algebraMap ℂ[X] (QuadRing h) h := by
  have := AdjoinRoot.eval₂_root (quadPoly h)
  rw [eval₂_quadPoly] at this
  rw [AdjoinRoot.algebraMap_eq]
  linear_combination this

/-- In the local ring at `(c, d)`, the image of `w − d` is a multiple of `t − c`,
provided `d ≠ 0`. -/
lemma quadRoot_sub_mem_span (hdne : d ≠ 0) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)} := by
  obtain ⟨q, hq⟩ : (X - C c) ∣ h - C (h.eval c) := X_sub_C_dvd_sub_C_eval
  have hsum : AdjoinRoot.root (quadPoly h) + algebraMap ℂ[X] (QuadRing h) (C d) ∈
      (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, map_add, quadEval_root, quadEval_algebraMap, eval_C]
    intro hzero
    exact hdne (by linear_combination hzero / 2)
  obtain ⟨y, hy⟩ := (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hsum⟩).exists_right_inv
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap (QuadRing h) _
    (algebraMap ℂ[X] (QuadRing h) q) * y, ?_⟩
  have hfactor : (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) *
      (AdjoinRoot.root (quadPoly h) + algebraMap ℂ[X] (QuadRing h) (C d)) =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) q := by
    have hroot := quadRing_root_sq h
    have hdC : algebraMap ℂ[X] (QuadRing h) (C d) ^ 2 =
        algebraMap ℂ[X] (QuadRing h) (C (h.eval c)) := by
      rw [← map_pow, ← C_pow, hd]
    rw [quadShift, ← map_mul, ← hq, map_sub]
    linear_combination hroot - hdC
  calc algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d))
      = algebraMap (QuadRing h) (quadLocalRing h c d hd)
          ((AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) *
            (AdjoinRoot.root (quadPoly h) + algebraMap ℂ[X] (QuadRing h) (C d))) * y := by
        rw [map_mul, mul_assoc, hy, mul_one]
    _ = algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c) *
          (algebraMap (QuadRing h) _ (algebraMap ℂ[X] (QuadRing h) q) * y) := by
        rw [hfactor, map_mul, mul_assoc]

/-- Every element of the point ideal becomes a multiple of `t − c` in the local ring,
when `d ≠ 0`. -/
lemma quadKer_le_span (hdne : d ≠ 0) (p : QuadRing h)
    (hp : p ∈ RingHom.ker (quadEval h c d hd)) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd) p ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)} := by
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h p
  rw [RingHom.mem_ker, map_add, map_mul, quadEval_algebraMap, quadEval_algebraMap,
    quadEval_root] at hp
  obtain ⟨qa, hqa⟩ : (X - C c) ∣ a - C (a.eval c) := X_sub_C_dvd_sub_C_eval
  obtain ⟨qb, hqb⟩ : (X - C c) ∣ b - C (b.eval c) := X_sub_C_dvd_sub_C_eval
  have ha : algebraMap ℂ[X] (QuadRing h) a =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qa +
        algebraMap ℂ[X] (QuadRing h) (C (a.eval c)) := by
    rw [quadShift, ← map_mul, ← map_add, ← hqa]
    ring_nf
  have hb : algebraMap ℂ[X] (QuadRing h) b =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qb +
        algebraMap ℂ[X] (QuadRing h) (C (b.eval c)) := by
    rw [quadShift, ← map_mul, ← map_add, ← hqb]
    ring_nf
  have hzero : algebraMap ℂ[X] (QuadRing h) (C (a.eval c)) +
      algebraMap ℂ[X] (QuadRing h) (C (b.eval c)) *
        algebraMap ℂ[X] (QuadRing h) (C d) = 0 := by
    rw [← map_mul, ← map_add, ← C_mul, ← C_add, hp]
    simp
  have hsplit : algebraMap ℂ[X] (QuadRing h) a +
      algebraMap ℂ[X] (QuadRing h) b * AdjoinRoot.root (quadPoly h) =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qa +
        algebraMap ℂ[X] (QuadRing h) b *
          (AdjoinRoot.root (quadPoly h) - algebraMap ℂ[X] (QuadRing h) (C d)) +
        algebraMap ℂ[X] (QuadRing h) (C d) *
          (quadShift h c * algebraMap ℂ[X] (QuadRing h) qb) := by
    linear_combination ha + algebraMap ℂ[X] (QuadRing h) (C d) * hb + hzero
  simp only [hsplit, map_add, map_mul]
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
  · exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · exact Ideal.mul_mem_left _ _ (quadRoot_sub_mem_span h c d hd hdne)
  · exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/-- **G09a-2e**: at an unramified point place, `t − c` generates the maximal ideal. -/
theorem quad_unramified_uniformizer (hc : h.eval c ≠ 0) :
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) =
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)} := by
  have hdne : d ≠ 0 := by
    intro hzero
    rw [hzero] at hd
    exact hc (by linear_combination -hd)
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (RingHom.ker (quadEval h c d hd)).primeCompl x
    have hmem : a ∈ RingHom.ker (quadEval h c d hd) :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (quadLocalRing h c d hd)
        (RingHom.ker (quadEval h c d hd)) a s).mp hx
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (quadKer_le_span h c d hd hdne a hmem)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (quadLocalRing h c d hd)
      (RingHom.ker (quadEval h c d hd)) (quadShift h c)).mpr (quadShift_mem_ker h c d hd)

/-- The differential of that uniformizer is `dt`. -/
theorem quad_unramified_D_uniformizer :
    KaehlerDifferential.D ℂ (QuadField h)
        ((algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c) :
          quadLocalRing h c d hd) : QuadField h) =
      KaehlerDifferential.D ℂ (QuadField h) (quadT h) := by
  have hcoe : ((algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c) :
      quadLocalRing h c d hd) : QuadField h) =
      quadT h - algebraMap ℂ (QuadField h) c := by
    show algebraMap (QuadRing h) (QuadField h) (quadShift h c) = _
    rw [quadShift, ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h),
      map_sub, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadField h), quadT]
  rw [hcoe, map_sub, Derivation.map_algebraMap, sub_zero]

/-- At an unramified point place, a differential `f·dt` is a multiple of the differential
of a uniformizer by the same `f`: the order of `dt` there is zero. -/
theorem quad_unramified_coeff (hc : h.eval c ≠ 0) (f : QuadField h) :
    ∃ u : quadLocalRing h c d hd,
      IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u} ∧
        f • KaehlerDifferential.D ℂ (QuadField h) (quadT h) =
          f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) :=
  ⟨algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c),
    quad_unramified_uniformizer h c d hd hc,
    by rw [quad_unramified_D_uniformizer]⟩

/-! ### Ramified point places (G09a-2f) -/

omit [Fact (Irreducible (quadRat h))] in
/-- A simple root splits off a factor that does not vanish there. -/
lemma exists_factor_of_root (hc : h.eval c = 0) :
    ∃ k : ℂ[X], h = (X - C c) * k ∧ k.eval c ≠ 0 := by
  obtain ⟨k, hk⟩ := (dvd_iff_isRoot (a := c) (p := h)).mpr hc
  refine ⟨k, hk, ?_⟩
  intro hk0
  obtain ⟨j, hj⟩ := (dvd_iff_isRoot (a := c) (p := k)).mpr hk0
  have hsq : (X - C c) * (X - C c) ∣ h := ⟨j, by rw [hk, hj]; ring⟩
  exact Polynomial.not_isUnit_X_sub_C c ((Fact.out : Squarefree h) _ hsq)

omit [Fact (Irreducible (quadRat h))] in
/-- At a ramified point place, `(t − c)·k = w²` with `k(c) ≠ 0`: the coordinate `t − c`
is the square of the uniformizer up to a unit. -/
lemma quad_ramified_shift_sq (hc : h.eval c = 0) :
    ∃ k : ℂ[X], k.eval c ≠ 0 ∧
      quadShift h c * algebraMap ℂ[X] (QuadRing h) k = AdjoinRoot.root (quadPoly h) ^ 2 := by
  obtain ⟨k, hk, hkc⟩ := exists_factor_of_root h c hc
  refine ⟨k, hkc, ?_⟩
  rw [quadShift, ← map_mul, ← hk, quadRing_root_sq]

/-- At a ramified point place, `t − c` is a multiple of `w` in the local ring. -/
lemma quadShift_mem_span_root (hc : h.eval c = 0) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c) ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by
  obtain ⟨k, hk, hkc⟩ := exists_factor_of_root h c hc
  have hkmem : algebraMap ℂ[X] (QuadRing h) k ∈
      (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_algebraMap]
    exact hkc
  obtain ⟨y, hy⟩ := (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hkmem⟩).exists_right_inv
  have hfactor : quadShift h c * algebraMap ℂ[X] (QuadRing h) k =
      AdjoinRoot.root (quadPoly h) * AdjoinRoot.root (quadPoly h) := by
    rw [quadShift, ← map_mul, ← hk, ← sq, quadRing_root_sq]
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap (QuadRing h) _
    (AdjoinRoot.root (quadPoly h)) * y, ?_⟩
  calc algebraMap (QuadRing h) (quadLocalRing h c d hd) (quadShift h c)
      = algebraMap (QuadRing h) (quadLocalRing h c d hd)
          (quadShift h c * algebraMap ℂ[X] (QuadRing h) k) * y := by
        rw [map_mul, mul_assoc, hy, mul_one]
    _ = algebraMap (QuadRing h) (quadLocalRing h c d hd) (AdjoinRoot.root (quadPoly h)) *
          (algebraMap (QuadRing h) _ (AdjoinRoot.root (quadPoly h)) * y) := by
        rw [hfactor, map_mul, mul_assoc]

/-- Every element of the point ideal becomes a multiple of `w` in the local ring, at a
ramified place. -/
lemma quadKer_le_span_root (hc : h.eval c = 0) (p : QuadRing h)
    (hp : p ∈ RingHom.ker (quadEval h c d hd)) :
    algebraMap (QuadRing h) (quadLocalRing h c d hd) p ∈
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by
  have hd0 : d = 0 := by
    have : d ^ 2 = 0 := by rw [hd, hc]
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h p
  rw [RingHom.mem_ker, map_add, map_mul, quadEval_algebraMap, quadEval_algebraMap,
    quadEval_root, hd0, mul_zero, add_zero] at hp
  obtain ⟨qa, hqa⟩ := (dvd_iff_isRoot (a := c) (p := a)).mpr hp
  have ha : algebraMap ℂ[X] (QuadRing h) a =
      quadShift h c * algebraMap ℂ[X] (QuadRing h) qa := by
    rw [quadShift, ← map_mul, ← hqa]
  rw [ha, map_add, map_mul, map_mul]
  refine Ideal.add_mem _ ?_ ?_
  · exact Ideal.mul_mem_right _ _ (quadShift_mem_span_root h c d hd hc)
  · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- **G09a-2f**: at a ramified point place, `w` generates the maximal ideal. -/
theorem quad_ramified_uniformizer (hc : h.eval c = 0) :
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) =
      Ideal.span {algebraMap (QuadRing h) (quadLocalRing h c d hd)
        (AdjoinRoot.root (quadPoly h))} := by
  have hd0 : d = 0 := by
    have : d ^ 2 = 0 := by rw [hd, hc]
    exact pow_eq_zero_iff two_ne_zero |>.mp this
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (RingHom.ker (quadEval h c d hd)).primeCompl x
    have hmem : a ∈ RingHom.ker (quadEval h c d hd) :=
      (IsLocalization.AtPrime.mk'_mem_maximal_iff (quadLocalRing h c d hd)
        (RingHom.ker (quadEval h c d hd)) a s).mp hx
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (quadKer_le_span_root h c d hd hc a hmem)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    refine (IsLocalization.AtPrime.to_map_mem_maximal_iff (quadLocalRing h c d hd)
      (RingHom.ker (quadEval h c d hd)) (AdjoinRoot.root (quadPoly h))).mpr ?_
    rw [RingHom.mem_ker, quadEval_root, hd0]

/-- The image of that uniformizer in the function field is the root `w`. -/
theorem quad_ramified_uniformizer_coe :
    ((algebraMap (QuadRing h) (quadLocalRing h c d hd) (AdjoinRoot.root (quadPoly h)) :
        quadLocalRing h c d hd) : QuadField h) = AdjoinRoot.root (quadRat h) := by
  show algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.root (quadPoly h)) = _
  rw [algebraMap_quadRing_apply, quadRingMap_root]

/-- At a ramified point place, `h'(t)` is invertible in the local ring: `c` is a simple
root of `h`. -/
theorem quad_ramified_derivative_isUnit (hc : h.eval c = 0) :
    IsUnit (algebraMap (QuadRing h) (quadLocalRing h c d hd)
      (algebraMap ℂ[X] (QuadRing h) h.derivative)) := by
  obtain ⟨k, hk, hkc⟩ := exists_factor_of_root h c hc
  have hderiv : h.derivative.eval c = k.eval c := by
    rw [hk, derivative_mul, derivative_sub, derivative_X, derivative_C]
    simp
  have hmem : algebraMap ℂ[X] (QuadRing h) h.derivative ∈
      (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_algebraMap, hderiv]
    exact hkc
  exact IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hmem⟩

omit [Fact (Squarefree h)] in
/-- At a ramified point place, reading `f·dt` against the uniformizer `w` multiplies the
coefficient by `w` and a unit: `2·f·w` after clearing `h'(t)`. This is `ord_v(dt) = 1`. -/
theorem quad_ramified_coeff (f : QuadField h) :
    algebraMap ℂ[X] (QuadField h) h.derivative •
        (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h)) =
      (2 * f * AdjoinRoot.root (quadRat h)) •
        KaehlerDifferential.D ℂ (QuadField h) (AdjoinRoot.root (quadRat h)) := by
  have hroot := quad_D_root h
  rw [smul_smul, mul_comm, ← smul_smul, ← hroot, smul_smul]
  congr 1
  ring

end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- G09a-2e for the family: at a point place over a `c` with `h_α(c) ≠ 0`, the coordinate
`t − c` is a uniformizer and its differential is `dt`. -/
theorem family_unramified_uniformizer (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c)
    (hc : (familyH m α).eval c ≠ 0) :
    IsLocalRing.maximalIdeal (quadLocalRing (familyH m α) c d hd) =
        Ideal.span {algebraMap (QuadRing (familyH m α)) (quadLocalRing (familyH m α) c d hd)
          (quadShift (familyH m α) c)} ∧
      KaehlerDifferential.D ℂ (QuadField (familyH m α))
          ((algebraMap (QuadRing (familyH m α)) (quadLocalRing (familyH m α) c d hd)
            (quadShift (familyH m α) c) : quadLocalRing (familyH m α) c d hd) :
              QuadField (familyH m α)) =
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) :=
  ⟨quad_unramified_uniformizer _ c d hd hc, quad_unramified_D_uniformizer _ c d hd⟩

omit hm ha in
/-- A root of `h_α` gives a point of the double cover with `d = 0`. -/
lemma familyH_root_point (c : ℂ) (hc : (familyH m α).eval c = 0) :
    (0 : ℂ) ^ 2 = (familyH m α).eval c := by
  rw [hc]; ring

/-- G09a-2f for the family: over a root of `h_α` the place is ramified, `w` generates its
maximal ideal, and `h_α'(t)` is a unit there, so `f·dt` reads as `2·f·w·dw` after clearing
that unit. -/
theorem family_ramified_uniformizer (c : ℂ) (hc : (familyH m α).eval c = 0) :
    IsLocalRing.maximalIdeal (quadLocalRing (familyH m α) c 0 (familyH_root_point c hc)) =
        Ideal.span {algebraMap (QuadRing (familyH m α))
          (quadLocalRing (familyH m α) c 0 (familyH_root_point c hc))
          (AdjoinRoot.root (quadPoly (familyH m α)))} ∧
      IsUnit (algebraMap (QuadRing (familyH m α))
        (quadLocalRing (familyH m α) c 0 (familyH_root_point c hc))
        (algebraMap ℂ[X] (QuadRing (familyH m α)) (familyH m α).derivative)) :=
  ⟨quad_ramified_uniformizer _ c 0 (familyH_root_point c hc) hc,
    quad_ramified_derivative_isUnit _ c 0 (familyH_root_point c hc) hc⟩

#print axioms quad_unramified_uniformizer
#print axioms quad_ramified_uniformizer
#print axioms family_ramified_uniformizer
#print axioms family_unramified_uniformizer

end CurveSymmetry
