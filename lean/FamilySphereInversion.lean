import FamilyTransport
import MobiusPair

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial OnePoint

lemma sphereInversion_involutive {c : ℂ} (hc : c ≠ 0) :
    Function.Involutive (sphereInversion c) := by
  intro p
  cases p using OnePoint.rec with
  | infty => simp [sphereInversion]
  | coe z =>
    by_cases hz : z = 0
    · simp [sphereInversion, hz]
    · simp only [sphereInversion, OnePoint.elim_some, ite_eq_right hz,
        ite_eq_right (div_ne_zero hc hz), OnePoint.coe_eq_coe]
      field_simp

private lemma inversion_degree_le (m : ℕ) (β c : ℂ) :
    (inversionFamily m β c).totalDegree ≤ m + 2 := by
  have hb (a b : ℕ) (k : ℂ) :
      (monomial (exponent a b) k : BPoly).totalDegree ≤ a + b := by
    simpa [Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent a b) k
  rw [inversionFamily, fourTermForm_monomial]
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le ((hb _ _ _).trans (by omega)) ((hb _ _ _).trans (by omega))
    · exact (hb _ _ _).trans (by omega)
  · exact (hb _ _ _).trans (by omega)

/-- Spherical inclusion yields the cleared polynomial identity, including the
source point zero where the rational affine formula has a pole. -/
theorem family_sphere_inversion_proportional {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m β) :
    ∃ k : ℂ, k ≠ 0 ∧ inversionFamily m β c = C k * familyPolynomial m α := by
  apply proportional_of_realLocus_subset (familyPolynomial_irreducible hm ha)
    (hinf := family_realLocus_infinite hm ha)
  · intro he
    have hcoef := (fourTermForm_coefficients hm
      (star c ^ m * (c * star c)) (c ^ m * (c * star c))
      (star c ^ m * star β) (c ^ m * β)).1
    change (inversionFamily m β c).coeff (exponent m 0) = _ at hcoef
    rw [he, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoef
    exact (mul_ne_zero (pow_ne_zero m (star_ne_zero.mpr hc))
      (mul_ne_zero hc (star_ne_zero.mpr hc))) hcoef.symm
  · intro z hz
    change planeEval z (star z) (inversionFamily m β c) = 0
    by_cases hz0 : z = 0
    · simp [hz0, inversionFamily, fourTermForm_eval, hm.ne']
    · have hzs : (z : Sphere) ∈ sphericalFamily m α := by
        rw [finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq]
        exact hz
      have ht := hmap (z : Sphere) hzs
      change (if z = 0 then ∞ else ((c / z : ℂ) : Sphere)) ∈ sphericalFamily m β at ht
      rw [ite_eq_right hz0] at ht
      rw [finite_mem_sphericalFamily_iff hm hb, ← family_locus_eq] at ht
      change planeEval (c / z) (star (c / z)) (familyPolynomial m β) = 0 at ht
      rw [inversionFamily_eval m β c hz0 (star_ne_zero.mpr hz0)]
      have hs : star (c / z) = star c / star z := map_div₀ (starRingEnd ℂ) c z
      rw [← hs, ht, mul_zero]
  · rw [family_degree hm]
    exact inversion_degree_le m β c

theorem family_sphere_inversion_parameter {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (ha : α ≠ star α) (hb : β ≠ star β)
    (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m β) :
    ‖c‖ = 1 ∧ β = α := by
  obtain ⟨k, _, he⟩ := family_sphere_inversion_proportional hm ha hb hc hmap
  exact family_inversion_parameter hm hα hβ hc he

theorem family_sphere_inversion_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0) :
    (∀ p ∈ sphericalFamily m α, sphereInversion c p ∈ sphericalFamily m α) ↔
      c ^ (2 * m) = star α ^ 2 := by
  constructor
  · intro hmap
    obtain ⟨k, _, he⟩ := family_sphere_inversion_proportional hm ha ha hc hmap
    exact (family_inversion_filter hm hα hc).mp ⟨k, he⟩
  · intro hroot p hp
    obtain ⟨k, he⟩ := (family_inversion_filter hm hα hc).mpr hroot
    cases p using OnePoint.rec with
    | infty =>
      simp only [sphereInversion, OnePoint.elim_infty]
      rw [finite_mem_sphericalFamily_iff hm ha]
      simp [extremalCurve, hm.ne']
    | coe z =>
      by_cases hz : z = 0
      · simp only [sphereInversion, hz, OnePoint.elim_some]
        exact infinity_mem_sphericalFamily hm ha
      · change (if z = 0 then ∞ else ((c / z : ℂ) : Sphere)) ∈ sphericalFamily m α
        rw [ite_eq_right hz]
        rw [finite_mem_sphericalFamily_iff hm ha, ← family_locus_eq] at hp ⊢
        change planeEval z (star z) (familyPolynomial m α) = 0 at hp
        change planeEval (c / z) (star (c / z)) (familyPolynomial m α) = 0
        have hev := congrArg (planeEval z (star z)) he
        rw [inversionFamily_eval m α c hz (star_ne_zero.mpr hz), map_mul,
          planeEval_C, hp, mul_zero] at hev
        have hs : star (c / z) = star c / star z := map_div₀ (starRingEnd ℂ) c z
        rw [hs]
        exact (mul_eq_zero.mp hev).resolve_left
          (pow_ne_zero _ (mul_ne_zero hz (star_ne_zero.mpr hz)))

/-- The root condition preserves membership in both directions on the whole
sphere, since inversion exchanges zero and infinity and is an involution. -/
theorem family_sphere_inversion_mem_iff {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0)
    (hroot : c ^ (2 * m) = star α ^ 2) (p : Sphere) :
    sphereInversion c p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  have hmap := (family_sphere_inversion_filter hm hα ha hc).mpr hroot
  constructor
  · intro hp
    simpa only [sphereInversion_involutive hc p] using hmap (sphereInversion c p) hp
  · exact hmap p

#print axioms sphereInversion_involutive
#print axioms family_sphere_inversion_parameter
#print axioms family_sphere_inversion_filter
#print axioms family_sphere_inversion_mem_iff

end CurveSymmetry
