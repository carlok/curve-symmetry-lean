import CartesianReal

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- An opposite symmetry squares to a translation, which must vanish.
Hence there is no nontrivial glide reflection. -/
theorem opposite_symmetry_no_glide {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {a b : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) : a * star b + b = 0 := by
  have ha := mul_star_eq_one_of_norm h.1
  apply no_translation_symmetry hP hd hne
  intro z hz
  have h2 := (h.2 (a * star z + b)).mpr ((h.2 z).mpr hz)
  have he : a * star (a * star z + b) + b = z + (a * star b + b) := by
    simp only [star_add, star_mul, star_star]
    linear_combination z * ha
  rwa [he] at h2

/-- Every opposite symmetry fixes `b/2`: it is a reflection in a line. -/
theorem opposite_symmetry_fixed_point {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hne : (realLocus P).Nonempty) {a b : ℂ}
    (h : OppositeSymmetry (realLocus P) a b) : a * star (b / 2) + b = b / 2 := by
  have hg := opposite_symmetry_no_glide hP hd hne h
  have hs : star (b / 2) = star b / 2 := by simp
  rw [hs]
  linear_combination hg / 2

/-- Lemma 3 for an actual Euclidean isometry of the real locus: the equation
transforms by a sign, and by `+1` for every orientation-reversing symmetry. -/
theorem isometry_sign_of_realLocus {P : BPoly} (hP : Irreducible P)
    (hd : 2 ≤ P.totalDegree) (hinf : (realLocus P).Infinite)
    (T : isometrySymmetryGroup P) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧
      (∀ z : ℂ, eval (fun i : Fin 2 => if i = 0 then T.val z else star (T.val z)) P =
        ε * eval (fun i : Fin 2 => if i = 0 then z else star z) P) ∧
      ((∃ a b : ℂ, ∀ z : ℂ, T.val z = a * star z + b) → ε = 1) := by
  have hT : ∀ z, T.val z ∈ realLocus P ↔ z ∈ realLocus P := T.prop
  rcases isometry_affine_forms T.val with ⟨a, b, ha, he⟩ | ⟨a, b, ha, he⟩
  · have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    have hnotopp : ¬ ∃ c d : ℂ, ∀ z : ℂ, T.val z = c * star z + d := by
      rintro ⟨c, d, hcd⟩
      exact direct_ne_opposite ha0 (fun z => (he z).symm.trans (hcd z))
    by_cases ha1 : a = 1
    · have hb : b = 0 := by
        apply no_translation_symmetry hP hd hinf.nonempty
        intro z hz
        have h := (hT z).mpr hz
        rwa [he, ha1, one_mul] at h
      refine ⟨1, Or.inl rfl, fun z => ?_, fun _ => rfl⟩
      rw [he, ha1, hb, one_mul, add_zero, one_mul]
    · have h1a : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
      set z0 := b / (1 - a) with hz0
      have hmap : ∀ z, T.val z = a * (z - z0) + z0 := by
        intro z
        rw [he, hz0]
        field_simp
        ring
      have hQ : Irreducible (shift z0 P) := hP.map (shiftEquiv z0).toMulEquiv
      have hQinf := realLocus_shift_infinite z0 hinf
      have hsym : ∀ z ∈ realLocus (shift z0 P), a * z ∈ realLocus (shift z0 P) := by
        intro z hz
        rw [mem_realLocus_shift] at hz ⊢
        have h := (hT (z + z0)).mpr hz
        rwa [hmap, add_sub_cancel_right] at h
      have hval : ∀ z, eval (fun i : Fin 2 => if i = 0 then T.val z else star (T.val z)) P =
          eval (fun i : Fin 2 => if i = 0 then z - z0 else star (z - z0))
            (rotate a (shift z0 P)) := by
        intro z
        rw [eval_rotate a ha, eval_shift, ← hmap]
      have hback : ∀ z, eval (fun i : Fin 2 => if i = 0 then z - z0 else star (z - z0))
          (shift z0 P) = eval (fun i : Fin 2 => if i = 0 then z else star z) P := by
        intro z
        rw [eval_shift, sub_add_cancel]
      rcases rotation_sign_of_realLocus hQ hQinf ha hsym with hr | hr
      · refine ⟨1, Or.inl rfl, fun z => ?_, fun h => (hnotopp h).elim⟩
        rw [hval, hr, hback, one_mul]
      · refine ⟨-1, Or.inr rfl, fun z => ?_, fun h => (hnotopp h).elim⟩
        rw [hval, hr, map_neg, hback, neg_one_mul]
  · have hS : OppositeSymmetry (realLocus P) a b := ⟨ha, fun z => by rw [← he]; exact hT z⟩
    have hfixed := opposite_symmetry_fixed_point hP hd hinf.nonempty hS
    set z0 := b / 2 with hz0
    have hmap : ∀ z, T.val z = a * star (z - z0) + z0 := by
      intro z
      rw [he, star_sub, mul_sub]
      linear_combination hfixed
    have hQ : Irreducible (shift z0 P) := hP.map (shiftEquiv z0).toMulEquiv
    have hQinf := realLocus_shift_infinite z0 hinf
    have hsym : ∀ z ∈ realLocus (shift z0 P), a * star z ∈ realLocus (shift z0 P) := by
      intro z hz
      rw [mem_realLocus_shift] at hz ⊢
      have h := (hT (z + z0)).mpr hz
      rwa [hmap, add_sub_cancel_right] at h
    have hfix := reflection_fixes_equation hQ (by rwa [shift_degree]) hQinf ha hsym
    refine ⟨1, Or.inl rfl, fun z => ?_, fun _ => rfl⟩
    have h := eval_reflect a (shift z0 P) (z - z0)
    rw [hfix, eval_shift, eval_shift, sub_add_cancel, ← hmap] at h
    rw [← h, one_mul]

lemma eval_complexifyReal (f : RPoly) (z : ℂ) :
    eval (fun i : Fin 2 => if i = 0 then z else star z) (complexifyReal f) =
      (eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f : ℂ) := by
  change eval _ (complexify (map Complex.ofRealHom f)) = _
  rw [eval_complexify, eval_real_map]

/-- Lemma 3 for the paper's real Cartesian equation and every actual isometry
preserving its zero set: `f ∘ T = ε f` with `ε = ±1`, and `ε = 1` whenever `T`
reverses orientation (each such `T` is a reflection by
`opposite_symmetry_fixed_point`). -/
theorem paper_isometry_sign {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (T : isometrySetGroup (cartesianLocus f)) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (∀ z : ℂ, eval (fun i : Fin 2 => if i = 0 then (T.val z).re else (T.val z).im) f =
        ε * eval (fun i : Fin 2 => if i = 0 then z.re else z.im) f) ∧
      ((∃ a b : ℂ, ∀ z : ℂ, T.val z = a * star z + b) → ε = 1) := by
  have hT : T.val ∈ isometrySymmetryGroup (complexifyReal f) := by
    rw [isometrySymmetryGroup, complexifyReal_locus]
    exact T.prop
  obtain ⟨ε, hε, hid, hopp⟩ := isometry_sign_of_realLocus (complexifyReal_irreducible hf)
    (by rwa [complexifyReal_degree]) (by rwa [complexifyReal_locus]) ⟨T.val, hT⟩
  rcases hε with rfl | rfl
  · refine ⟨1, Or.inl rfl, fun z => ?_, fun _ => rfl⟩
    have h := hid z
    rw [eval_complexifyReal, eval_complexifyReal] at h
    exact_mod_cast h
  · refine ⟨-1, Or.inr rfl, fun z => ?_, fun h => ?_⟩
    · have h := hid z
      rw [eval_complexifyReal, eval_complexifyReal] at h
      exact_mod_cast h
    · have h1 := hopp h
      norm_num at h1

#print axioms opposite_symmetry_no_glide
#print axioms opposite_symmetry_fixed_point
#print axioms isometry_sign_of_realLocus
#print axioms paper_isometry_sign

end CurveSymmetry
