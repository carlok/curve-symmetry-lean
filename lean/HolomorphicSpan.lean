import HolomorphicBasis
import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Holomorphic differentials are spanned by `tⁱ·dt/w` (G09b-3d)

First step (G09b-3d-1): a differential `f·dt` regular at every point place has
`f·w` in every point place's local ring, hence — `ℂ[t][W]/(W² − h)` being a
domain equal to the intersection of its localizations at maximal ideals — in
`ℂ[t][W]/(W² − h)` itself: `f·w = a(t) + b(t)·w`, that is, `f = a/w + b`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section Point

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]

/-- An element of the function field lying in the local ring of every point place comes from
`ℂ[t][W]/(W² − h)`: that ring is the intersection of its localizations at maximal ideals. -/
theorem quad_mem_range_of_forall_local (g : QuadField h)
    (hg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c), g ∈ quadLocalRing h c d hd) :
    ∃ y : QuadRing h, algebraMap (QuadRing h) (QuadField h) y = g := by
  have hbot := MaximalSpectrum.iInf_localization_eq_bot (QuadRing h) (QuadField h)
  have hmem : g ∈ (⊥ : Subalgebra (QuadRing h) (QuadField h)) := by
    rw [← hbot, Algebra.mem_iInf]
    rintro ⟨P, hP⟩
    obtain ⟨c, d, hd, rfl⟩ := (quadRing_isMaximal_iff h P).mp hP
    exact hg c d hd
  rw [Algebra.mem_bot] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

/-- **G09b-3d-1**: if `f·dt` is regular at every point place, then `f·w = a(t) + b(t)·w` for
polynomials `a` and `b`. -/
theorem quad_regular_points_coeff (f : QuadField h)
    (hreg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h))) :
    ∃ a b : ℂ[X], f * AdjoinRoot.root (quadRat h) =
      algebraMap ℂ[X] (QuadField h) a +
        algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  have hlocal : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      f * AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
    intro c d hd
    by_cases hc : h.eval c = 0
    · exact (isRegularAt_ramified h c d hd hc f).mp (hreg c d hd)
    · exact Subalgebra.mul_mem _ ((isRegularAt_unramified h c d hd hc f).mp (hreg c d hd))
        (quadLocal_root_mem h c d hd)
  obtain ⟨y, hy⟩ := quad_mem_range_of_forall_local h _ hlocal
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
  refine ⟨a, b, ?_⟩
  have hroot : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.root (quadPoly h)) =
      AdjoinRoot.root (quadRat h) := by
    rw [algebraMap_quadRing_apply, quadRingMap_root]
  rw [← hy, map_add, map_mul, hroot,
    ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h),
    ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]

end Point

#print axioms quad_regular_points_coeff

end CurveSymmetry
