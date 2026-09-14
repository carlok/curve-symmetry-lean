import FamilySphereClassification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace CurveSymmetry
set_option autoImplicit false

noncomputable def arcParameter (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem arcParameter_norm (θ : ℝ) : ‖arcParameter θ‖ = 1 := by
  simp [arcParameter, Complex.norm_exp]

theorem arcParameter_im_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    0 < (arcParameter θ).im := by
  simpa [arcParameter, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos] using
    Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2

theorem arcParameter_nonreal {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    arcParameter θ ≠ star (arcParameter θ) := by
  intro he
  have hi := congrArg Complex.im he
  have hp := arcParameter_im_pos hθ
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

theorem arcParameter_injective : Set.InjOn arcParameter (Set.Ioo 0 Real.pi) := by
  intro θ hθ φ hφ he
  apply Real.strictAntiOn_cos.injOn ⟨hθ.1.le, hθ.2.le⟩ ⟨hφ.1.le, hφ.2.le⟩
  have hr := congrArg Complex.re he
  simpa [arcParameter, Complex.exp_mul_I, ← Complex.ofReal_sin, ← Complex.ofReal_cos] using hr

theorem arcParameter_ne_conjugate {θ φ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hφ : φ ∈ Set.Ioo 0 Real.pi) :
    arcParameter φ ≠ star (arcParameter θ) := by
  intro he
  have hi := congrArg Complex.im he
  have hp := arcParameter_im_pos hθ
  have hq := arcParameter_im_pos hφ
  simp only [Complex.star_def, Complex.conj_im] at hi
  linarith

/-- The upper semicircle is an injective family even modulo both ambient parities. -/
theorem family_arc_equivalence_iff {m : ℕ} (hm : 2 ≤ m) {θ φ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (hφ : φ ∈ Set.Ioo 0 Real.pi) :
    ((∃ g : MobiusMatrix, (fun p : Sphere => g • p) ''
        sphericalFamily m (arcParameter θ) = sphericalFamily m (arcParameter φ)) ∨
     (∃ g : MobiusMatrix, (fun p : Sphere => g • OnePoint.map (star : ℂ → ℂ) p) ''
        sphericalFamily m (arcParameter θ) = sphericalFamily m (arcParameter φ))) ↔ θ = φ := by
  rw [family_mobius_equivalence_iff hm (arcParameter_nonreal hθ)
      (arcParameter_nonreal hφ) (arcParameter_norm θ) (arcParameter_norm φ),
    family_anti_mobius_equivalence_iff hm (arcParameter_nonreal hθ)
      (arcParameter_nonreal hφ) (arcParameter_norm θ) (arcParameter_norm φ)]
  constructor
  · rintro (he | he)
    · exact (arcParameter_injective hφ hθ he).symm
    · exact (arcParameter_ne_conjugate hθ hφ he).elim
  · intro he
    exact Or.inl (congrArg arcParameter he.symm)

#print axioms family_arc_equivalence_iff
end CurveSymmetry
