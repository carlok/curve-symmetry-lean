import InversionDenominators

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

abbrev CoordinateNonzero (i : Fin 2) := {v : Fin 2 → ℂ // v i ≠ 0}

/-- Coordinate inversion is continuous into the Zariski affine plane when
restricted to the domain on which its denominator is nonzero. -/
theorem continuous_invertCoordinate (i : Fin 2) :
    Continuous (fun v : CoordinateNonzero i => invertCoordinate i v.val) := by
  apply continuous_iff_isClosed.mpr
  intro S hS
  have he : S = {v | ∀ P ∈ vanishingIdeal ℂ S, eval v P = 0} :=
    hS.closure_eq.symm.trans (affineZariski_closure S)
  have hpre : (fun v : CoordinateNonzero i => invertCoordinate i v.val) ⁻¹' S =
      ⋂ P ∈ vanishingIdeal ℂ S,
        {v : CoordinateNonzero i | eval (invertCoordinate i v.val) P = 0} := by
    ext v
    conv_lhs => rw [he]
    simp
  rw [hpre]
  apply isClosed_biInter
  intro P _
  obtain ⟨Q, hQ⟩ := inversion_zero_set_numerator i P
  have hz : {v : CoordinateNonzero i | eval (invertCoordinate i v.val) P = 0} =
      {v : CoordinateNonzero i | eval v.val Q = 0} := by
    ext v
    exact hQ v.val v.property
  rw [hz]
  exact (affineZariski_polynomial_zero_closed Q).preimage continuous_subtype_val

def inversionOnDomain (i : Fin 2) (v : CoordinateNonzero i) : CoordinateNonzero i :=
  ⟨invertCoordinate i v.val, by simpa [invertCoordinate] using inv_ne_zero v.property⟩

theorem inversionOnDomain_involutive (i : Fin 2) :
    Function.Involutive (inversionOnDomain i) := by
  intro v
  apply Subtype.ext
  exact invertCoordinate_involutive i v.val

theorem continuous_inversionOnDomain (i : Fin 2) : Continuous (inversionOnDomain i) :=
  (continuous_invertCoordinate i).subtype_mk _

/-- A genuine Zariski homeomorphism of the coordinate-divisor complement.
The source topology is induced from the affine spectrum, not Euclidean. -/
def coordinateInversionHomeomorph (i : Fin 2) : CoordinateNonzero i ≃ₜ CoordinateNonzero i where
  toFun := inversionOnDomain i
  invFun := inversionOnDomain i
  left_inv := inversionOnDomain_involutive i
  right_inv := inversionOnDomain_involutive i
  continuous_toFun := continuous_inversionOnDomain i
  continuous_invFun := continuous_inversionOnDomain i

#print axioms continuous_invertCoordinate
#print axioms coordinateInversionHomeomorph

end
end CurveSymmetry
