import AffineZariskiTopology

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- Invert exactly one coordinate. The continuity results will restrict this
total formula to the domain on which that coordinate is nonzero. -/
noncomputable def invertCoordinate (i : Fin 2) (v : Fin 2 → ℂ) (j : Fin 2) : ℂ :=
  if j = i then (v j)⁻¹ else v j

theorem invertCoordinate_involutive (i : Fin 2) : Function.Involutive (invertCoordinate i) := by
  intro v
  ext j
  by_cases h : j = i <;> simp [invertCoordinate, h]

/-- Every polynomial after one-coordinate inversion has a polynomial numerator
and a power of that coordinate as denominator. The equality is asserted only
where the denominator is nonzero; no degree bound is needed here. -/
theorem inversion_clear_denominator (i : Fin 2) (P : BPoly) :
    ∃ n : ℕ, ∃ Q : BPoly, ∀ v : Fin 2 → ℂ, v i ≠ 0 →
      eval v Q = (v i) ^ n * eval (invertCoordinate i v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨0, C a, by intro v _; simp⟩
  | add P R hP hR =>
      obtain ⟨n, Q, hQ⟩ := hP
      obtain ⟨k, S, hS⟩ := hR
      refine ⟨n + k, Q * X i ^ k + S * X i ^ n, ?_⟩
      intro v hv
      simp only [map_add, map_mul, map_pow, eval_X]
      rw [hQ v hv, hS v hv, pow_add]
      ring
  | mul_X P j hP =>
      obtain ⟨n, Q, hQ⟩ := hP
      by_cases hj : j = i
      · subst j
        refine ⟨n + 1, Q, ?_⟩
        intro v hv
        rw [hQ v hv]
        have hi : invertCoordinate i v i = (v i)⁻¹ := by simp [invertCoordinate]
        simp only [map_mul, eval_X, hi, pow_succ]
        field_simp
      · refine ⟨n, Q * X j, ?_⟩
        intro v hv
        simp only [map_mul, eval_X, invertCoordinate, if_neg hj]
        rw [hQ v hv]
        ring

/-- On the inversion domain, inverse images of polynomial zero sets are
polynomial zero sets. This algebraic statement is independent of topology. -/
theorem inversion_zero_set_numerator (i : Fin 2) (P : BPoly) :
    ∃ Q : BPoly, ∀ v : Fin 2 → ℂ, v i ≠ 0 →
      (eval (invertCoordinate i v) P = 0 ↔ eval v Q = 0) := by
  obtain ⟨n, Q, hQ⟩ := inversion_clear_denominator i P
  refine ⟨Q, ?_⟩
  intro v hv
  rw [hQ v hv, mul_eq_zero]
  simp [pow_ne_zero n hv]

#print axioms inversion_clear_denominator
#print axioms inversion_zero_set_numerator

end CurveSymmetry
