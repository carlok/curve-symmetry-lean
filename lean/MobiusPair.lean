import SphereGeometry

namespace CurveSymmetry

set_option autoImplicit false
open OnePoint

lemma mobius_zero_to_infinity_iff (g : MobiusMatrix) :
    g • ((0 : ℂ) : Sphere) = ∞ ↔ g 1 1 = 0 := by
  rw [mobius_finite_formula]
  simp

lemma mobius_fixes_zero_iff (g : MobiusMatrix) :
    g • ((0 : ℂ) : Sphere) = ((0 : ℂ) : Sphere) ↔ g 0 1 = 0 := by
  rw [mobius_finite_formula]
  by_cases hd : g 1 1 = 0
  · have hb : g 0 1 ≠ 0 := by
      intro hb
      have hn := g.det_ne_zero
      simp [Matrix.det_fin_two, hd, hb] at hn
    simp [hd, hb]
  · simp [hd]

lemma mobius_infinity_to_zero_iff (g : MobiusMatrix) :
    g • (∞ : Sphere) = ((0 : ℂ) : Sphere) ↔ g 0 0 = 0 := by
  rw [mobius_infinity_formula]
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := by
      intro ha
      have hn := g.det_ne_zero
      simp [Matrix.det_fin_two, hc, ha] at hn
    simp [hc, ha]
  · simp [hc]

/-- The stabilizer of the unordered pair `0,∞` is exactly the diagonal and
antidiagonal matrices. Applying this lemma to our curve will require a proof
that an arbitrary curve equivalence preserves its singular pair. -/
theorem mobius_pair_matrix_iff (g : MobiusMatrix) :
    (fun p : Sphere => g • p) '' {((0 : ℂ) : Sphere), ∞} = {((0 : ℂ) : Sphere), ∞} ↔
      (g 0 1 = 0 ∧ g 1 0 = 0) ∨ (g 1 1 = 0 ∧ g 0 0 = 0) := by
  rw [Set.image_pair, Set.pair_eq_pair_iff, mobius_fixes_zero_iff,
    OnePoint.smul_infty_eq_self_iff, mobius_zero_to_infinity_iff, mobius_infinity_to_zero_iff]

def sphereDilation (c : ℂ) : Sphere → Sphere := OnePoint.map (fun z : ℂ => c * z)

noncomputable def sphereInversion (c : ℂ) (p : Sphere) : Sphere :=
  p.elim ((0 : ℂ) : Sphere) (fun z : ℂ => if z = 0 then ∞ else ((c / z : ℂ) : Sphere))

lemma mobius_diagonal_action (g : MobiusMatrix) (hb : g 0 1 = 0) (hc : g 1 0 = 0) :
    g 0 0 / g 1 1 ≠ 0 ∧ ∀ p : Sphere, g • p = sphereDilation (g 0 0 / g 1 1) p := by
  have hn := g.det_ne_zero
  simp only [Matrix.det_fin_two, hb, hc, zero_mul, sub_zero, ne_eq, mul_eq_zero, not_or] at hn
  refine ⟨div_ne_zero hn.1 hn.2, ?_⟩
  intro p
  cases p using OnePoint.rec with
  | infty => simp [mobius_infinity_formula, hc, sphereDilation]
  | coe z =>
    simp [mobius_finite_formula, hb, hc, hn.2, sphereDilation, div_eq_mul_inv,
      mul_comm, mul_assoc]

lemma mobius_antidiagonal_action (g : MobiusMatrix) (ha : g 0 0 = 0) (hd : g 1 1 = 0) :
    g 0 1 / g 1 0 ≠ 0 ∧ ∀ p : Sphere, g • p = sphereInversion (g 0 1 / g 1 0) p := by
  have hn := g.det_ne_zero
  simp only [Matrix.det_fin_two, ha, hd, zero_mul, zero_sub, neg_ne_zero, ne_eq,
    mul_eq_zero, not_or] at hn
  refine ⟨div_ne_zero hn.1 hn.2, ?_⟩
  intro p
  cases p using OnePoint.rec with
  | infty => simp [mobius_infinity_formula, ha, hn.2, sphereInversion]
  | coe z =>
    by_cases hz : z = 0
    · simp [mobius_finite_formula, hd, hz, sphereInversion]
    · have he : g 0 1 / (g 1 0 * z) = g 0 1 / g 1 0 / z := by
        field_simp
      simp [mobius_finite_formula, ha, hd, hn.2, hz, sphereInversion, he]

/-- A conditional group-theoretic reduction, not the missing curve-completeness
theorem: pair preservation is explicit here and must later be derived. -/
theorem mobius_forms_of_preserves_pair (g : MobiusMatrix)
    (hpair : (fun p : Sphere => g • p) '' {((0 : ℂ) : Sphere), ∞} = {((0 : ℂ) : Sphere), ∞}) :
    ∃ c : ℂ, c ≠ 0 ∧ ((∀ p : Sphere, g • p = sphereDilation c p) ∨
      (∀ p : Sphere, g • p = sphereInversion c p)) := by
  rcases (mobius_pair_matrix_iff g).mp hpair with ⟨hb, hc⟩ | ⟨hd, ha⟩
  · obtain ⟨hn, he⟩ := mobius_diagonal_action g hb hc
    exact ⟨g 0 0 / g 1 1, hn, Or.inl he⟩
  · obtain ⟨hn, he⟩ := mobius_antidiagonal_action g ha hd
    exact ⟨g 0 1 / g 1 0, hn, Or.inr he⟩

#print axioms mobius_pair_matrix_iff
#print axioms mobius_forms_of_preserves_pair

end CurveSymmetry
