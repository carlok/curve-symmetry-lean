import PaperBounds
import Mathlib.Algebra.MvPolynomial.PDeriv

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

noncomputable def planeEval (x y : ℂ) : BPoly →+* ℂ :=
  eval (fun i : Fin 2 => if i = 0 then x else y)

@[simp] lemma planeEval_C (x y c : ℂ) : planeEval x y (C c) = c := by simp [planeEval]
@[simp] lemma planeEval_X_zero (x y : ℂ) : planeEval x y (X 0) = x := by simp [planeEval]
@[simp] lemma planeEval_X_one (x y : ℂ) : planeEval x y (X 1) = y := by simp [planeEval]

/-- The affine hypersurface Jacobian condition, using Mathlib's formal partial derivatives. -/
def JacobianSingular (P : BPoly) (x y : ℂ) : Prop :=
  planeEval x y P = 0 ∧ planeEval x y (pderiv 0 P) = 0 ∧ planeEval x y (pderiv 1 P) = 0

noncomputable def binaryForm (m : ℕ) (a b : ℂ) : BPoly := C a * X 0 ^ m + C b * X 1 ^ m

noncomputable def fourTermForm (m : ℕ) (a b c d : ℂ) : BPoly :=
  binaryForm m a b + X 0 * X 1 * binaryForm m c d

lemma binaryForm_euler (m : ℕ) (a b : ℂ) :
    X 0 * pderiv 0 (binaryForm m a b) + X 1 * pderiv 1 (binaryForm m a b) =
      (m : BPoly) * binaryForm m a b := by
  cases m with
  | zero => simp [binaryForm]
  | succ n =>
      simp only [binaryForm, map_add, pderiv_C_mul, pderiv_pow]
      simp [pow_succ]
      ring

lemma fourTermForm_euler (m : ℕ) (a b c d : ℂ) :
    X 0 * pderiv 0 (fourTermForm m a b c d) +
      X 1 * pderiv 1 (fourTermForm m a b c d) =
      (m : BPoly) * fourTermForm m a b c d + 2 * X 0 * X 1 * binaryForm m c d := by
  have hlow := binaryForm_euler m a b
  have hhigh := binaryForm_euler m c d
  simp only [fourTermForm, map_add, pderiv_mul, pderiv_X, Pi.single_apply, Fin.isValue,
    show (1 : Fin 2) ≠ 0 by decide, show (0 : Fin 2) ≠ 1 by decide, ↓reduceIte, zero_mul,
    mul_zero, one_mul, mul_one, zero_add, add_zero]
  linear_combination hlow + (X 0 : BPoly) * X 1 * hhigh

lemma fourTermForm_eval (m : ℕ) (a b c d x y : ℂ) :
    planeEval x y (fourTermForm m a b c d) =
      a * x ^ m + b * y ^ m + x * y * (c * x ^ m + d * y ^ m) := by
  simp [fourTermForm, binaryForm]

lemma fourTermForm_not_singular_on_torus {m : ℕ} {a b c d x y : ℂ}
    (hdet : a * d - b * c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    ¬ JacobianSingular (fourTermForm m a b c d) x y := by
  rintro ⟨hp, hpx, hpy⟩
  have he := congrArg (planeEval x y) (fourTermForm_euler m a b c d)
  simp only [map_add, map_mul, planeEval_X_zero, planeEval_X_one, hpx, hpy, hp,
    mul_zero, zero_add, map_ofNat, binaryForm, map_pow, planeEval_C] at he
  have hv : c * x ^ m + d * y ^ m = 0 := by
    apply (mul_eq_zero.mp he.symm).resolve_left
    exact mul_ne_zero (mul_ne_zero (by norm_num) hx) hy
  rw [fourTermForm_eval, hv, mul_zero, add_zero] at hp
  have hz : (a * d - b * c) * x ^ m = 0 := by linear_combination d * hp - b * hv
  exact (mul_ne_zero hdet (pow_ne_zero m hx)) hz

lemma fourTermForm_origin_singular {m : ℕ} (hm : 2 ≤ m) (a b c d : ℂ) :
    JacobianSingular (fourTermForm m a b c d) 0 0 := by
  have hm0 : m ≠ 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  simp [JacobianSingular, fourTermForm, binaryForm, hm0, hm1]

/-- A nonsingular coefficient matrix leaves exactly the origin as an affine
Jacobian singularity in this four-term family. -/
theorem fourTermForm_singular_iff {m : ℕ} (hm : 2 ≤ m) {a b c d x y : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hdet : a * d - b * c ≠ 0) :
    JacobianSingular (fourTermForm m a b c d) x y ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hs
    have hp := hs.1
    rw [fourTermForm_eval] at hp
    by_cases hx : x = 0
    · refine ⟨hx, ?_⟩
      simp only [hx, zero_pow (by omega : m ≠ 0), mul_zero, zero_mul, zero_add, add_zero] at hp
      exact (pow_eq_zero_iff (by omega : m ≠ 0)).mp ((mul_eq_zero.mp hp).resolve_left hb)
    · by_cases hy : y = 0
      · simp only [hy, zero_pow (by omega : m ≠ 0), mul_zero, zero_mul, add_zero] at hp
        exact ((mul_ne_zero ha (pow_ne_zero m hx)) hp).elim
      · exact (fourTermForm_not_singular_on_torus hdet hx hy hs).elim
  · rintro ⟨rfl, rfl⟩
    exact fourTermForm_origin_singular hm a b c d

lemma family_fourTerm (m : ℕ) (α : ℂ) :
    familyPolynomial m α = fourTermForm m α (star α) 1 1 := by
  simp only [familyPolynomial, fourTermForm, binaryForm, map_one, one_mul]
  ring

/-- The only affine singular point of the extremal family is `(0,0)`. -/
theorem family_affine_singular_iff {m : ℕ} (hm : 2 ≤ m) {α x y : ℂ} (ha : α ≠ star α) :
    JacobianSingular (familyPolynomial m α) x y ↔ x = 0 ∧ y = 0 := by
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  rw [family_fourTerm]
  apply fourTermForm_singular_iff hm ha0 (star_ne_zero.mpr ha0)
  simpa using sub_ne_zero.mpr ha

/-- The equation in reciprocal coordinates `u=1/X`, `v=1/Y`. -/
noncomputable def familyInfinityPolynomial (m : ℕ) (α : ℂ) : BPoly :=
  fourTermForm m 1 1 (star α) α

theorem family_infinity_singular_iff {m : ℕ} (hm : 2 ≤ m) {α u v : ℂ} (ha : α ≠ star α) :
    JacobianSingular (familyInfinityPolynomial m α) u v ↔ u = 0 ∧ v = 0 := by
  apply fourTermForm_singular_iff hm one_ne_zero one_ne_zero
  simpa using sub_ne_zero.mpr ha

#print axioms fourTermForm_singular_iff
#print axioms family_affine_singular_iff
#print axioms family_infinity_singular_iff

end CurveSymmetry
