import QuadraticIntegralClosure

/-!
# The integral closure of the double cover is a Dedekind domain (G07b-2a)

When `W² − h` is irreducible over `ℂ(t)`, the field `L = ℂ(t)[W]/(W² − h)` is a
finite separable extension of `ℂ(t) = Frac(ℂ[t])`. Mathlib's integral-closure
theory then makes the integral closure of `ℂ[t]` in `L` a Dedekind domain with
fraction field `L`. G07b-1 describes its elements as `a + b·w`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section

variable (h : ℂ[X]) [Fact (Irreducible (quadRat h))]

instance quadField_finiteDimensional : FiniteDimensional (RatFunc ℂ) (QuadField h) :=
  (AdjoinRoot.powerBasis (quadRat_monic h).ne_zero).finite

theorem quad_integralClosure_isDedekindDomain :
    IsDedekindDomain (integralClosure ℂ[X] (QuadField h)) :=
  integralClosure.isDedekindDomain ℂ[X] (RatFunc ℂ) (QuadField h)

theorem quad_integralClosure_isFractionRing :
    IsFractionRing (integralClosure ℂ[X] (QuadField h)) (QuadField h) :=
  integralClosure.isFractionRing_of_finite_extension (RatFunc ℂ) (QuadField h)

theorem quad_mem_integralClosure_iff (hsq : Squarefree h) (x : QuadField h) :
    x ∈ integralClosure ℂ[X] (QuadField h) ↔ ∃ a b : ℂ[X],
      x = algebraMap ℂ[X] (QuadField h) a +
        algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) :=
  (mem_integralClosure_iff _ _).trans (quad_isIntegral_iff h hsq x)

end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

instance quadRat_familyH_fact : Fact (Irreducible (quadRat (familyH m α))) :=
  ⟨by rw [quadRat_familyH]; exact familyQuadraticRat_irreducible_of hm.out ha.out⟩

/-- G07b-2a for the family: the integral closure of `ℂ[t]` in the function field
of `V_α` is a Dedekind domain with that fraction field, consisting of the
elements `a + b·w` with `a, b ∈ ℂ[t]`. -/
theorem family_integralClosure_dedekind :
    IsDedekindDomain (integralClosure ℂ[X] (QuadField (familyH m α))) ∧
      IsFractionRing (integralClosure ℂ[X] (QuadField (familyH m α)))
        (QuadField (familyH m α)) ∧
      ∀ x : QuadField (familyH m α), x ∈ integralClosure ℂ[X] (QuadField (familyH m α)) ↔
        ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadField (familyH m α)) a +
          algebraMap ℂ[X] (QuadField (familyH m α)) b *
            AdjoinRoot.root (quadRat (familyH m α)) :=
  ⟨quad_integralClosure_isDedekindDomain _, quad_integralClosure_isFractionRing _,
    quad_mem_integralClosure_iff _ (familyH_squarefree_of hm.out ha.out)⟩

#print axioms quad_integralClosure_isDedekindDomain
#print axioms family_integralClosure_dedekind

end CurveSymmetry
