import MixedCornerClosure

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- The second mixed chart uses the ordered coordinates `(1/Y, X)`.
Away from `Y = ∞` its equation is equivalent to the original affine equation. -/
lemma other_mixed_zero_iff (m : ℕ) (α : ℂ) {v x : ℂ} (hv : v ≠ 0) :
    planeEval v x (familyMixedPolynomial m (star α) α) = 0 ↔
      planeEval x v⁻¹ (familyPolynomial m α) = 0 := by
  rw [← family_other_mixed_chart m α hv, mul_eq_zero]
  simp [pow_ne_zero _ hv]

/-- Actual affine curve points with `Y ≠ 0` give exactly the punctured
second mixed chart; the coordinate exchange is explicit in both directions. -/
theorem other_mixed_affine_points_image (m : ℕ) (α : ℂ) :
    (fun z : Fin 2 → ℂ => ![(z 1)⁻¹, z 0]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 1 ≠ 0} =
      {w : Fin 2 → ℂ | eval w (familyMixedPolynomial m (star α) α) = 0 ∧
        w 0 ≠ 0} := by
  have he (z : Fin 2 → ℂ) : ![z 0, z 1] = z := by
    ext i
    fin_cases i <;> rfl
  have hep (x y : ℂ) : planeEval x y = eval ![x, y] := by
    unfold planeEval
    congr 1
    funext i
    fin_cases i <;> rfl
  apply Set.Subset.antisymm
  · rintro w ⟨z, ⟨hz, hy⟩, rfl⟩
    refine ⟨?_, inv_ne_zero hy⟩
    have h := (other_mixed_zero_iff m α (inv_ne_zero hy)).mpr
      (show planeEval (z 0) ((z 1)⁻¹)⁻¹ (familyPolynomial m α) = 0 by
        simpa only [inv_inv, hep, he] using hz)
    simpa only [hep] using h
  · rintro w ⟨hw, hv⟩
    refine ⟨![w 1, (w 0)⁻¹], ⟨?_, inv_ne_zero hv⟩, ?_⟩
    · have h := (other_mixed_zero_iff m α hv).mp
        (show planeEval (w 0) (w 1) (familyMixedPolynomial m (star α) α) = 0 by
          simpa only [hep, he] using hw)
      simpa only [hep] using h
    · simpa using he w

/-- Closure of original affine curve points expressed in the second mixed
chart. This uses Mathlib's affine spectral Zariski topology, not a newly
declared topology on the product of projective lines. -/
theorem other_mixed_affine_points_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 1)⁻¹, z 0]) ''
      {z | eval z (familyPolynomial m α) = 0 ∧ z 1 ≠ 0}) =
      PrimeSpectrum.zeroLocus ({familyMixedPolynomial m (star α) α} : Set BPoly) := by
  have hi := other_mixed_affine_points_image m α
  have he := congrArg (Set.image affineSpectrumPoint) hi
  rw [Set.image_image] at he
  rw [he]
  have hs : {w : Fin 2 → ℂ |
      eval w (familyMixedPolynomial m (star α) α) = 0 ∧ w 0 ≠ 0} =
      {w : Fin 2 → ℂ |
        eval w (familyMixedPolynomial m (star α) α) = 0 ∧ eval w (X 0) ≠ 0} := by simp
  rw [hs]
  exact punctured_complex_points_closure _ _ coordinate_zero_irreducible
    (mixed_not_dvd_coordinate hm (star α) α)

/-- The chart origin representing `(0,∞)` is in the closure of the original
affine curve in this chart. Global projective gluing remains separate. -/
theorem other_mixed_corner_mem_affine_closure {m : ℕ} (hm : 0 < m) (α : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure ((fun z : Fin 2 → ℂ => affineSpectrumPoint ![(z 1)⁻¹, z 0]) ''
        {z | eval z (familyPolynomial m α) = 0 ∧ z 1 ≠ 0}) := by
  rw [other_mixed_affine_points_closure hm α]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyMixedPolynomial m (star α) α) = 0
  simp [familyMixedPolynomial, hm.ne']

#print axioms other_mixed_affine_points_closure
#print axioms other_mixed_corner_mem_affine_closure

end CurveSymmetry
