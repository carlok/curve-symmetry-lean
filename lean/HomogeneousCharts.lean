import PolynomialDifferential
import Mathlib.Analysis.Calculus.FDeriv.Analytic

namespace CurveSymmetry

set_option autoImplicit false
open Filter
open scoped Topology

def homogeneousChart (v : Fin 2 → ℂ) : HomogeneousPairs :=
  (![v 0, 1], ![v 1, 1])

noncomputable def homogeneousRatios (q : HomogeneousPairs) : Fin 2 → ℂ :=
  ![q.1 0 / q.1 1, q.2 0 / q.2 1]

private lemma pair_normalize (x : Fin 2 → ℂ) (hx : x 1 ≠ 0) :
    x = x 1 • (![x 0 / x 1, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- On a homogeneous chart, the equation and its full differential vanish
exactly when the dehomogenized equation and its differential vanish. The proof
uses the actual local normalization map and its nonzero denominators. -/
theorem criticalZero_homogeneousChart (F : HomogeneousPairs → ℂ) (d : ℕ)
    (hscale : ∀ (a b : ℂ) (q : HomogeneousPairs),
      F (a • q.1, b • q.2) = a ^ d * b ^ d * F q) (v : Fin 2 → ℂ) :
    CriticalZero F (homogeneousChart v) ↔ CriticalZero (F ∘ homogeneousChart) v := by
  have hchart : Differentiable ℂ homogeneousChart := by
    unfold homogeneousChart
    apply Differentiable.prodMk
    all_goals
      apply differentiable_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
  have hratio : DifferentiableAt ℂ homogeneousRatios (homogeneousChart v) := by
    unfold homogeneousRatios homogeneousChart
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i <;> dsimp <;>
      fun_prop (disch := norm_num)
  have hback : homogeneousRatios (homogeneousChart v) = v := by
    ext i
    fin_cases i <;> simp [homogeneousRatios, homogeneousChart]
  constructor
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    simpa using hd.comp v (hchart v).hasFDerivAt
  · rintro ⟨hz, hd⟩
    refine ⟨hz, ?_⟩
    let A : HomogeneousPairs → ℂ := fun q => q.1 1 ^ d * q.2 1 ^ d
    let H : HomogeneousPairs → ℂ := (F ∘ homogeneousChart) ∘ homogeneousRatios
    have hH : HasFDerivAt H (0 : HomogeneousPairs →L[ℂ] ℂ) (homogeneousChart v) := by
      have hh := hd
      rw [← hback] at hh
      simpa [H] using hh.comp (homogeneousChart v) hratio.hasFDerivAt
    have hA : DifferentiableAt ℂ A (homogeneousChart v) := by
      dsimp [A]
      fun_prop
    have hH0 : H (homogeneousChart v) = 0 := by simpa [H, hback] using hz
    have hprod : HasFDerivAt (fun q => A q * H q)
        (0 : HomogeneousPairs →L[ℂ] ℂ) (homogeneousChart v) := by
      convert hA.hasFDerivAt.mul hH using 1 <;> first | rfl | skip
      apply ContinuousLinearMap.ext
      intro w
      change (0 : ℂ) = A (homogeneousChart v) * 0 + H (homogeneousChart v) * _
      rw [hH0]
      ring
    apply hprod.congr_of_eventuallyEq
    have hopen : IsOpen {q : HomogeneousPairs | q.1 1 ≠ 0 ∧ q.2 1 ≠ 0} := by
      apply IsOpen.inter <;> exact isOpen_ne.preimage (by fun_prop)
    have hmem : homogeneousChart v ∈ {q : HomogeneousPairs | q.1 1 ≠ 0 ∧ q.2 1 ≠ 0} := by
      simp [homogeneousChart]
    filter_upwards [hopen.mem_nhds hmem] with q hq
    have he := hscale (q.1 1) (q.2 1) (homogeneousChart (homogeneousRatios q))
    have hx := pair_normalize q.1 hq.1
    have hy := pair_normalize q.2 hq.2
    simpa [A, H, homogeneousChart, homogeneousRatios, ← hx, ← hy] using he

/-- The same chart bridge after independent invertible changes in the two
coordinate blocks. In particular this covers all four standard charts. -/
theorem criticalZero_reparametrizedChart (F : HomogeneousPairs → ℂ) (d : ℕ)
    (hscale : ∀ (a b : ℂ) (q : HomogeneousPairs),
      F (a • q.1, b • q.2) = a ^ d * b ^ d * F q)
    (e f : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ)) (v : Fin 2 → ℂ) :
    CriticalZero F (e (homogeneousChart v).1, f (homogeneousChart v).2) ↔
      CriticalZero (fun w => F (e (homogeneousChart w).1, f (homogeneousChart w).2)) v := by
  let T := e.prodCongr f
  have hs (a b : ℂ) (q : HomogeneousPairs) :
      (F ∘ T) (a • q.1, b • q.2) = a ^ d * b ^ d * (F ∘ T) q := by
    simpa [T, Function.comp_def] using hscale a b (T q)
  have he : ∀ q : HomogeneousPairs, F (T q) = 1 * (F ∘ T) q := by simp
  have ht := criticalZero_transport T (F := F ∘ T) (G := F) one_ne_zero he (homogeneousChart v)
  exact ht.trans (criticalZero_homogeneousChart (F ∘ T) d hs v)

/-- Exchanging the two coordinates of a homogeneous pair. -/
noncomputable def reverseCoordinates : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 2 => ℂ) (Equiv.swap 0 1)).toContinuousLinearEquiv

lemma reverseCoordinates_apply (x : Fin 2 → ℂ) :
    reverseCoordinates x = ![x 1, x 0] := by
  ext i
  fin_cases i <;> simp [reverseCoordinates, LinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft']

lemma familyBihomogeneous_scale (m : ℕ) (α a b : ℂ) (q : HomogeneousPairs) :
    familyBihomogeneous m α (a • q.1) (b • q.2) =
      a ^ (m + 1) * b ^ (m + 1) * familyBihomogeneous m α q.1 q.2 := by
  rw [familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
  ring

theorem family_critical_affine_iff (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![x, 1], ![y, 1]) ↔ JacobianSingular (familyPolynomial m α) x y := by
  have h := criticalZero_homogeneousChart
    (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) (m + 1)
    (familyBihomogeneous_scale m α) ![x, y]
  have he : (fun v : Fin 2 → ℂ => familyBihomogeneous m α (homogeneousChart v).1
      (homogeneousChart v).2) = fun v => MvPolynomial.eval v (familyPolynomial m α) := by
    funext v
    rw [homogeneousChart, familyBihomogeneous_affine, planeEval_eq_eval]
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  rw [jacobianSingular_iff_criticalZero]
  simp only [Function.comp_def, he] at h
  convert h using 1
  rfl

theorem family_critical_chart_iff (m : ℕ) (α : ℂ) (P : BPoly)
    (e f : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ))
    (he : ∀ v : Fin 2 → ℂ,
      familyBihomogeneous m α (e ![v 0, 1]) (f ![v 1, 1]) = MvPolynomial.eval v P)
    (x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (e ![x, 1], f ![y, 1]) ↔ JacobianSingular P x y := by
  have h := criticalZero_reparametrizedChart
    (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) (m + 1)
    (familyBihomogeneous_scale m α) e f ![x, y]
  rw [jacobianSingular_iff_criticalZero]
  simp only [homogeneousChart, funext he] at h
  convert h using 1
  rfl

theorem family_critical_reciprocal_iff (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![1, x], ![1, y]) ↔ JacobianSingular (familyInfinityPolynomial m α) x y := by
  have he (v : Fin 2 → ℂ) :
      familyBihomogeneous m α (reverseCoordinates ![v 0, 1])
        (reverseCoordinates ![v 1, 1]) = MvPolynomial.eval v (familyInfinityPolynomial m α) := by
    simp only [reverseCoordinates_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, familyBihomogeneous_reciprocal, planeEval_eq_eval]
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  simpa only [reverseCoordinates_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] using family_critical_chart_iff m α _ reverseCoordinates reverseCoordinates he x y

theorem family_critical_mixed_iff (m : ℕ) (α x y : ℂ) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (![1, x], ![y, 1]) ↔ JacobianSingular (familyMixedPolynomial m α (star α)) x y := by
  let e := ContinuousLinearEquiv.refl ℂ (Fin 2 → ℂ)
  have he (v : Fin 2 → ℂ) :
      familyBihomogeneous m α (reverseCoordinates ![v 0, 1])
        (e ![v 1, 1]) = MvPolynomial.eval v (familyMixedPolynomial m α (star α)) := by
    simp only [e, ContinuousLinearEquiv.refl_apply, reverseCoordinates_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      familyBihomogeneous_mixed, planeEval_eq_eval]
    have hv : ![v 0, v 1] = v := by ext i; fin_cases i <;> rfl
    rw [hv]
  simpa only [e, ContinuousLinearEquiv.refl_apply, reverseCoordinates_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
    family_critical_chart_iff m α _ reverseCoordinates e he x y

#print axioms criticalZero_homogeneousChart
#print axioms criticalZero_reparametrizedChart
#print axioms family_critical_affine_iff
#print axioms family_critical_reciprocal_iff
#print axioms family_critical_mixed_iff

end CurveSymmetry
