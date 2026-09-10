import ReciprocalCornerClosure

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

private lemma vector_eta (z : Fin 2 → ℂ) : ![z 0, z 1] = z := by
  ext i
  fin_cases i <;> rfl

private lemma planeEval_vector (x y : ℂ) : planeEval x y = eval ![x, y] := by
  unfold planeEval
  congr 1
  funext i
  fin_cases i <;> rfl

lemma mixed_vector_zero_iff (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ) (hw : w 0 ≠ 0) :
    eval w (familyMixedPolynomial m α (star α)) = 0 ↔
      eval ![(w 0)⁻¹, w 1] (familyPolynomial m α) = 0 := by
  have h := family_mixed_chart m α (y := w 1) hw
  rw [planeEval_vector, planeEval_vector, vector_eta] at h
  rw [← h, mul_eq_zero]
  simp [pow_ne_zero _ hw]

lemma reciprocal_vector_zero_iff (m : ℕ) (α : ℂ) (w : Fin 2 → ℂ)
    (h0 : w 0 ≠ 0) (h1 : w 1 ≠ 0) :
    eval w (familyInfinityPolynomial m α) = 0 ↔
      eval ![(w 0)⁻¹, (w 1)⁻¹] (familyPolynomial m α) = 0 := by
  have h := family_reciprocal_chart m α h0 h1
  rw [planeEval_vector, planeEval_vector, vector_eta] at h
  rw [← h, mul_eq_zero]
  simp [pow_ne_zero _ (mul_ne_zero h0 h1)]

/-- Inverting the first coordinate identifies original affine points with
`X ≠ 0` and the punctured first mixed chart, in both directions. -/
theorem mixed_affine_points_image (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 0)⁻¹, z 1]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyMixedPolynomial m α (star α)) = 0 ∧
        w 0 ≠ 0} := by
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, h0⟩, rfl⟩
    refine ⟨(mixed_vector_zero_iff m α _ (inv_ne_zero h0)).mpr ?_, inv_ne_zero h0⟩
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      inv_inv, vector_eta] using hz
  · rintro w ⟨hw, h0⟩
    refine ⟨![(w 0)⁻¹, w 1],
      ⟨(mixed_vector_zero_iff m α w h0).mp hw, inv_ne_zero h0⟩, ?_⟩
    simpa using vector_eta w

/-- Simultaneous inversion identifies original affine points off both axes
with the reciprocal chart off both axes. No zero denominator is included. -/
theorem reciprocal_affine_points_image (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 0)⁻¹, (z 1)⁻¹]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0 ∧ z 1 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyInfinityPolynomial m α) = 0 ∧
        w 0 ≠ 0 ∧ w 1 ≠ 0} := by
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, h0, h1⟩, rfl⟩
    refine ⟨(reciprocal_vector_zero_iff m α _ (inv_ne_zero h0)
      (inv_ne_zero h1)).mpr ?_, inv_ne_zero h0, inv_ne_zero h1⟩
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      inv_inv, vector_eta] using hz
  · rintro w ⟨hw, h0, h1⟩
    refine ⟨![(w 0)⁻¹, (w 1)⁻¹],
      ⟨(reciprocal_vector_zero_iff m α w h0 h1).mp hw,
        inv_ne_zero h0, inv_ne_zero h1⟩, ?_⟩
    simpa using vector_eta w

/-- The first mixed chart is the affine spectral closure of original curve
points expressed in that chart. Global projective gluing is not asserted. -/
theorem mixed_affine_points_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 0)⁻¹, z 1]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyMixedPolynomial m α (star α)} : Set BPoly) := by
  have he := congrArg (Set.image affineSpectrumPoint) (mixed_affine_points_image m α)
  rw [Set.image_image] at he
  rw [he]
  simpa using punctured_complex_points_closure _ _ coordinate_zero_irreducible
    (mixed_not_dvd_coordinate hm α (star α))

/-- The reciprocal chart is the affine spectral closure of original curve
points off both axes, expressed in reciprocal coordinates. -/
theorem reciprocal_affine_points_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 0)⁻¹, (z 1)⁻¹]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 0 ≠ 0 ∧ z 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyInfinityPolynomial m α} : Set BPoly) := by
  have he := congrArg (Set.image affineSpectrumPoint) (reciprocal_affine_points_image m α)
  rw [Set.image_image] at he
  rw [he]
  exact reciprocal_chart_complex_closure hm α

#print axioms mixed_affine_points_closure
#print axioms reciprocal_affine_points_closure

end CurveSymmetry
