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
    have hroot : AdjoinRoot.root (quadPoly h) ^ 2 = algebraMap ℂ[X] (QuadRing h) h := by
      have := AdjoinRoot.eval₂_root (quadPoly h)
      rw [eval₂_quadPoly] at this
      rw [AdjoinRoot.algebraMap_eq]
      linear_combination this
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

#print axioms quad_unramified_uniformizer
#print axioms family_unramified_uniformizer

end CurveSymmetry
