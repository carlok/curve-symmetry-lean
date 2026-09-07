import HomogeneousDifferential
import Mathlib.Analysis.Calculus.FDeriv.Pi

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- The differential specified by the formal partial derivatives, as a genuine
continuous linear map on the finite coordinate space. -/
noncomputable def polynomialDifferential {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) : (σ → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, eval x (pderiv i P) • ContinuousLinearMap.proj i

theorem polynomial_hasFDerivAt {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (fun y => eval y P) (polynomialDifferential P x) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
      convert (hasFDerivAt_const (𝕜 := 𝕜) c x) using 1 <;>
        first | rfl | (ext v; simp [polynomialDifferential])
  | add P Q hP hQ =>
      convert hP.add hQ using 1 <;> first | rfl | (ext v; simp [polynomialDifferential, add_mul, Finset.sum_add_distrib])
  | mul_X P i hP =>
      have hi := (ContinuousLinearMap.proj i : (σ → 𝕜) →L[𝕜] 𝕜).hasFDerivAt (x := x)
      convert hP.mul hi using 1 <;> first | rfl | (ext v; simp [polynomialDifferential, pderiv_X,
        Pi.single_apply, apply_ite, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_comm, mul_left_comm])

theorem polynomialDifferential_eq_zero_iff {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    polynomialDifferential P x = 0 ↔ ∀ i, eval x (pderiv i P) = 0 := by
  classical
  constructor
  · intro h i
    have hv := congrArg (fun L : (σ → 𝕜) →L[𝕜] 𝕜 => L (Pi.single i 1)) h
    simpa [polynomialDifferential, Pi.single_apply] using hv
  · intro h
    ext v
    simp [polynomialDifferential, h]

theorem criticalZero_polynomial_iff {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    CriticalZero (fun y => eval y P) x ↔
      eval x P = 0 ∧ ∀ i, eval x (pderiv i P) = 0 := by
  constructor
  · rintro ⟨hz, hd⟩
    exact ⟨hz, (polynomialDifferential_eq_zero_iff P x).mp
      ((polynomial_hasFDerivAt P x).unique hd)⟩
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    have he := (polynomialDifferential_eq_zero_iff P x).mpr hd
    simpa only [he] using polynomial_hasFDerivAt P x

lemma planeEval_eq_eval (x y : ℂ) (P : BPoly) :
    planeEval x y P = eval ![x, y] P := by
  have he : (fun i : Fin 2 => if i = 0 then x else y) = ![x, y] := by
    ext i
    fin_cases i <;> simp
  simp only [planeEval, he]

/-- The exact bridge to the chart Jacobian predicate used in the earlier local
singularity calculations. -/
theorem jacobianSingular_iff_criticalZero (P : BPoly) (x y : ℂ) :
    JacobianSingular P x y ↔ CriticalZero (fun z => eval z P) ![x, y] := by
  rw [criticalZero_polynomial_iff]
  simp only [JacobianSingular, planeEval_eq_eval, Fin.forall_fin_two]

#print axioms polynomial_hasFDerivAt
#print axioms criticalZero_polynomial_iff
#print axioms jacobianSingular_iff_criticalZero

end CurveSymmetry
