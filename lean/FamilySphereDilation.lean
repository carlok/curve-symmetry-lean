import FamilyTransport
import MobiusPair

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial OnePoint

lemma fourTermForm_totalDegree_le (m : ℕ) (a b c d : ℂ) :
    (fourTermForm m a b c d).totalDegree ≤ m + 2 := by
  rw [fourTermForm_monomial]
  have h (i j : ℕ) (k : ℂ) :
      (monomial (exponent i j) k : BPoly).totalDegree ≤ i + j := by
    simpa [Function.id_def, exponent_degree] using totalDegree_monomial_le (exponent i j) k
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      exact max_le ((h m 0 a).trans (by omega)) ((h 0 m b).trans (by omega))
    · exact (h (m + 1) 1 c).trans (by omega)
  · exact (h 1 (m + 1) d).trans (by omega)

theorem family_sphere_dilation_proportional {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m β) :
    ∃ k : ℂ, k ≠ 0 ∧ dilate c (familyPolynomial m β) = C k * familyPolynomial m α := by
  apply proportional_of_realLocus_subset (familyPolynomial_irreducible hm ha)
  · intro he
    have ht := (fourTermForm_coefficients hm (c ^ m * β)
      (star c ^ m * star β) (c ^ m * (c * star c)) (star c ^ m * (c * star c))).2.2.1
    rw [← dilate_family_fourTerm, he, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at ht
    exact (mul_ne_zero (pow_ne_zero m hc) (mul_ne_zero hc (star_ne_zero.mpr hc))) ht.symm
  · exact family_realLocus_infinite hm ha
  · intro z hz
    have hp : (z : Sphere) ∈ sphericalFamily m α :=
      (finite_mem_sphericalFamily_iff hm ha z).mpr ((family_locus_eq m α) ▸ hz)
    have hq := hmap (z : Sphere) hp
    change eval _ (dilate c (familyPolynomial m β)) = 0
    rw [eval_dilate]
    change c * z ∈ realLocus (familyPolynomial m β)
    exact (family_locus_eq m β).symm ▸
      ((finite_mem_sphericalFamily_iff hm hb (c * z)).mp hq)
  · rw [dilate_family_fourTerm, family_degree hm]
    exact fourTermForm_totalDegree_le _ _ _ _ _

theorem family_sphere_dilation_parameter {m : ℕ} (hm : 0 < m) {α β c : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1)
    (hc : c ≠ 0)
    (hmap : ∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m β) :
    ‖c‖ = 1 ∧ β = α := by
  obtain ⟨k, _, hk⟩ := family_sphere_dilation_proportional hm ha hb hc hmap
  exact family_dilation_parameter hm hα hβ hc hk

/-- Exact test on the actual sphere, including infinity. -/
theorem family_sphere_dilation_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∀ p ∈ sphericalFamily m α, sphereDilation c p ∈ sphericalFamily m α) ↔
      c ^ (2 * m) = 1 := by
  constructor
  · intro hmap
    obtain ⟨k, _, hk⟩ := family_sphere_dilation_proportional hm ha ha hc hmap
    exact (family_dilation_filter hm hα hc).mp ⟨k, hk⟩
  · intro hroot p hp
    obtain ⟨k, hk⟩ := (family_dilation_filter hm hα hc).mpr hroot
    cases p using OnePoint.rec with
    | infty => simpa [sphereDilation] using infinity_mem_sphericalFamily hm ha
    | coe z =>
      have hz : z ∈ realLocus (familyPolynomial m α) :=
        (family_locus_eq m α).symm ▸ ((finite_mem_sphericalFamily_iff hm ha z).mp hp)
      apply (finite_mem_sphericalFamily_iff hm ha (c * z)).mpr
      rw [← family_locus_eq]
      change eval _ (familyPolynomial m α) = 0
      rw [← eval_dilate, hk, map_mul, hz, mul_zero]

theorem family_sphere_dilation_mem_iff {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (ha : α ≠ star α) (hα : ‖α‖ = 1) (hc : c ≠ 0)
    (hroot : c ^ (2 * m) = 1) (p : Sphere) :
    sphereDilation c p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m α := by
  constructor
  · intro hp
    have hi : (c⁻¹) ^ (2 * m) = 1 := by rw [inv_pow, hroot, inv_one]
    have hback := (family_sphere_dilation_filter hm ha hα (inv_ne_zero hc)).mpr hi
      (sphereDilation c p) hp
    have he : sphereDilation c⁻¹ (sphereDilation c p) = p := by
      cases p using OnePoint.rec <;> simp [sphereDilation, hc]
    rwa [he] at hback
  · exact (family_sphere_dilation_filter hm ha hα hc).mpr hroot p

#print axioms family_sphere_dilation_mem_iff
#print axioms family_sphere_dilation_parameter
#print axioms family_sphere_dilation_filter

end CurveSymmetry
