import FamilyEuclidean
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section

/-- The actual Cartesian expression printed in the paper. -/
def quinticValue (z : ℂ) : ℝ :=
  (z.re ^ 2 + z.im ^ 2) * (z.re ^ 3 - 3 * z.re * z.im ^ 2) -
    3 * z.re ^ 2 * z.im + z.im ^ 3

theorem quinticValue_eq (z : ℂ) :
    quinticValue z = (z ^ 3 * ((‖z‖ : ℂ) ^ 2 + Complex.I)).re := by
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  simp only [quinticValue, pow_succ, pow_zero, one_mul, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  rw [← pow_two ‖z‖, hn]
  ring

def sixtyDegreeCoefficient : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / 3)

theorem sixtyDegree_norm : ‖sixtyDegreeCoefficient‖ = 1 := by
  simp [sixtyDegreeCoefficient, Complex.norm_exp]

theorem sixtyDegree_cube : sixtyDegreeCoefficient ^ 3 = -1 := by
  rw [sixtyDegreeCoefficient, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have he : (3 : ℂ) * ((Real.pi : ℂ) * Complex.I / 3) = Real.pi * Complex.I := by ring
  rw [he, Complex.exp_pi_mul_I]

theorem sixtyDegree_primitive : IsPrimitiveRoot sixtyDegreeCoefficient 6 := by
  change IsPrimitiveRoot (Complex.exp ((Real.pi : ℂ) * Complex.I / 3)) 6
  convert Complex.isPrimitiveRoot_exp 6 (by decide) using 1
  congr 1
  norm_num
  ring

theorem quintic_sixtyDegree_negates (z : ℂ) :
    quinticValue (sixtyDegreeCoefficient * z) = -quinticValue z := by
  rw [quinticValue_eq, quinticValue_eq, mul_pow, sixtyDegree_cube,
    norm_mul, sixtyDegree_norm, one_mul]
  simp

theorem quintic_locus_eq :
    {z : ℂ | quinticValue z = 0} = extremalCurve 3 Complex.I := by
  ext z
  change quinticValue z = 0 ↔ _
  rw [quinticValue_eq]
  rfl

/-- Six isometries, all direct, for the printed quintic locus. -/
theorem quintic_isometry_count :
    Nat.card (isometrySetGroup {z : ℂ | quinticValue z = 0}) = 6 := by
  rw [quintic_locus_eq]
  exact family_isometry_card (by decide) (by
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi) (by simp)

/-- Exact order of the stated actual Euclidean rotation, not only its coefficient. -/
theorem sixtyDegree_isometry_order :
    orderOf (affineDirectIsometry sixtyDegreeCoefficient 0 sixtyDegree_norm) = 6 := by
  let f := affineDirectIsometry sixtyDegreeCoefficient 0 sixtyDegree_norm
  have hp : ∀ n : ℕ, ∀ z : ℂ, (f ^ n) z = sixtyDegreeCoefficient ^ n * z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ]
      change (f ^ n) (f z) = _
      rw [ih]
      simp [f, pow_succ, mul_assoc]
  have he : orderOf f = orderOf sixtyDegreeCoefficient := by
    rw [orderOf_eq_orderOf_iff]
    intro n
    constructor
    · intro h
      have hz := congrArg (fun k : ℂ ≃ᵢ ℂ => k 1) h
      simpa [hp] using hz
    · intro h
      ext z
      simp [hp, h]
  exact he.trans sixtyDegree_primitive.eq_orderOf.symm

#print axioms sixtyDegree_isometry_order
#print axioms quinticValue_eq
#print axioms quintic_sixtyDegree_negates
#print axioms sixtyDegree_primitive
#print axioms quintic_isometry_count
end
end CurveSymmetry
