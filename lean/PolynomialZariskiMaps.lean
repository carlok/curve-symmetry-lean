import AffineZariskiTopology

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- The point map whose two coordinates are the given polynomials. -/
noncomputable def polynomialPointMap (F : Fin 2 → BPoly) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => eval v (F i)

theorem polynomialPointMap_eval (F : Fin 2 → BPoly) (v : Fin 2 → ℂ) (P : BPoly) :
    eval (polynomialPointMap F v) P = eval v (eval₂ C F P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simpa only [eval₂_add, map_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
      simp only [map_mul, eval_X, eval₂_mul, eval₂_X, polynomialPointMap]
      rw [hP]

noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

/-- Polynomial coordinate maps are continuous for the affine Zariski topology.
No Euclidean-continuity theorem or global topology instance is used. -/
theorem polynomialPointMap_continuous (F : Fin 2 → BPoly) :
    Continuous (polynomialPointMap F) := by
  apply continuous_iff_isClosed.mpr
  intro S hS
  have he : S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} :=
    hS.closure_eq.symm.trans (affineZariski_closure S)
  have hpre : polynomialPointMap F ⁻¹' S =
      ⋂ P ∈ vanishingIdeal ℂ S, {v : Fin 2 → ℂ | eval v (eval₂ C F P) = 0} := by
    ext v
    conv_lhs => rw [he]
    simp [polynomialPointMap_eval]
  rw [hpre]
  exact isClosed_biInter (fun P _ => affineZariski_polynomial_zero_closed (eval₂ C F P))

#print axioms polynomialPointMap_continuous

end
end CurveSymmetry
