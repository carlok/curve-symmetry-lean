import FamilyMobiusPullback
import FamilyTransport

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial
open OnePoint

private lemma degree_add_bound (i : Fin 2) {p q : BPoly} {n : ℕ}
    (hp : p.degreeOf i ≤ n) (hq : q.degreeOf i ≤ n) : (p + q).degreeOf i ≤ n :=
  (degreeOf_add_le i p q).trans (max_le hp hq)

private lemma degree_mul_bound (i : Fin 2) {p q : BPoly} {a b : ℕ}
    (hp : p.degreeOf i ≤ a) (hq : q.degreeOf i ≤ b) : (p * q).degreeOf i ≤ a + b :=
  (degreeOf_mul_le i p q).trans (Nat.add_le_add hp hq)

private lemma degree_pow_bound (i : Fin 2) {p : BPoly} {a : ℕ}
    (hp : p.degreeOf i ≤ a) (n : ℕ) : (p ^ n).degreeOf i ≤ n * a :=
  (degreeOf_pow_le i p n).trans (Nat.mul_le_mul_left n hp)

private lemma degree_affine_bound (i j : Fin 2) (a b : ℂ) :
    (C a * X j + C b : BPoly).degreeOf i ≤ if i = j then 1 else 0 := by
  calc
    _ ≤ max ((C a * X j : BPoly).degreeOf i) ((C b : BPoly).degreeOf i) :=
      degreeOf_add_le i _ _
    _ ≤ max ((X j : BPoly).degreeOf i) 0 :=
      max_le_max (degreeOf_C_mul_le _ i a) (by simp)
    _ = _ := by simp [degreeOf_X]

private lemma biform_degree_bound (i : Fin 2) (m : ℕ) (β : ℂ)
    (u v s t : BPoly) {a b : ℕ} (hu : u.degreeOf i ≤ a) (hv : v.degreeOf i ≤ a)
    (hs : s.degreeOf i ≤ b) (ht : t.degreeOf i ≤ b) :
    (C β * u ^ m * v * t ^ (m + 1) + u ^ (m + 1) * s * t ^ m +
      C (star β) * v ^ (m + 1) * s ^ m * t + u * v ^ m * s ^ (m + 1)).degreeOf i ≤
        (m + 1) * (a + b) := by
  apply degree_add_bound i (degree_add_bound i (degree_add_bound i ?_ ?_) ?_) ?_
  · have h := degree_mul_bound i (degree_mul_bound i
      ((degreeOf_C_mul_le _ i β).trans (degree_pow_bound i hu m)) hv)
      (degree_pow_bound i ht (m + 1))
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i (degree_pow_bound i hu (m + 1)) hs)
      (degree_pow_bound i ht m)
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i
      ((degreeOf_C_mul_le _ i (star β)).trans (degree_pow_bound i hv (m + 1)))
      (degree_pow_bound i hs m)) ht
    convert h using 1
    ring
  · have h := degree_mul_bound i (degree_mul_bound i hu (degree_pow_bound i hv m))
      (degree_pow_bound i hs (m + 1))
    convert h using 1
    ring

/-- Arbitrary product-projective pullback never exceeds degree `m+1` in either
affine variable. The total degree can be larger than the source total degree. -/
theorem familyMobiusPullback_degreeOf_le (m : ℕ) (β : ℂ) (g : MobiusMatrix) (i : Fin 2) :
    (familyMobiusPullback m β g).degreeOf i ≤ m + 1 := by
  have h := biform_degree_bound i m β (mobiusX g 0) (mobiusX g 1) (mobiusY g 0) (mobiusY g 1)
    (degree_affine_bound i 0 (g 0 0) (g 0 1))
    (degree_affine_bound i 0 (g 1 0) (g 1 1))
    (degree_affine_bound i 1 (star (g 0 0)) (star (g 0 1)))
    (degree_affine_bound i 1 (star (g 1 0)) (star (g 1 1)))
  fin_cases i <;> simpa [familyMobiusPullback] using h

lemma familyMobiusPullback_one (m : ℕ) (α : ℂ) :
    familyMobiusPullback m α 1 = familyPolynomial m α := by
  simp [familyMobiusPullback, mobiusX, mobiusY, familyPolynomial, pow_succ]
  ring

/-- The two separate affine degrees are both exactly `m+1`. -/
theorem family_degreeOf {m : ℕ} (hm : 0 < m) (α : ℂ) (i : Fin 2) :
    (familyPolynomial m α).degreeOf i = m + 1 := by
  apply Nat.le_antisymm
  · rw [← familyMobiusPullback_one m α]
    exact familyMobiusPullback_degreeOf_le m α 1 i
  · have hcoeff := fourTermForm_coefficients hm α (star α) 1 1
    rw [← family_fourTerm] at hcoeff
    fin_cases i
    · have hs : exponent (m + 1) 1 ∈ (familyPolynomial m α).support := by
        rw [mem_support_iff, hcoeff.2.2.1]
        exact one_ne_zero
      simpa [exponent] using monomial_le_degreeOf (0 : Fin 2) hs
    · have hs : exponent 1 (m + 1) ∈ (familyPolynomial m α).support := by
        rw [mem_support_iff, hcoeff.2.2.2]
        exact one_ne_zero
      simpa [exponent] using monomial_le_degreeOf (1 : Fin 2) hs

private lemma constant_of_degreeOf_zero {S : BPoly} (h : ∀ i, S.degreeOf i = 0) :
    S = C (S.coeff 0) := by
  apply MvPolynomial.ext
  intro d
  by_cases hd : d = 0
  · simp [hd]
  · have hs : d ∉ S.support := by
      intro hs
      apply hd
      ext i
      have hi := monomial_le_degreeOf i hs
      simpa [h i] using Nat.eq_zero_of_le_zero (by simpa [h i] using hi)
    have hc : S.coeff d = 0 := by simpa only [mem_support_iff, not_not] using hs
    rw [hc, coeff_C_of_ne_zero hd]

/-- Separate degree bounds, not a total-degree shortcut, remove the extra factor. -/
theorem proportional_of_family_dvd {m : ℕ} (hm : 0 < m) (α : ℂ) {Q : BPoly}
    (hQ : Q ≠ 0) (hdiv : familyPolynomial m α ∣ Q)
    (hdeg : ∀ i, Q.degreeOf i ≤ m + 1) :
    ∃ c : ℂ, c ≠ 0 ∧ Q = C c * familyPolynomial m α := by
  have hP : familyPolynomial m α ≠ 0 := by
    apply ne_zero_of_degreeOf_ne_zero (i := 0)
    rw [family_degreeOf hm]
    omega
  obtain ⟨S, hS⟩ := hdiv
  have hs0 : S ≠ 0 := by intro h; apply hQ; simp [hS, h]
  have hsdeg : ∀ i, S.degreeOf i = 0 := by
    intro i
    have hmul := degreeOf_mul_eq (n := i) hP hs0
    rw [← hS, family_degreeOf hm] at hmul
    have hi := hdeg i
    omega
  have hcS := constant_of_degreeOf_zero hsdeg
  refine ⟨S.coeff 0, ?_, ?_⟩
  · intro hc
    exact hs0 (by simpa [hc] using hcS)
  · rw [hS, hcS, mul_comm]
    simp

private lemma positive_real_mem_family_iff (m : ℕ) (β : ℂ) {r : ℝ} (hr : 0 < r) :
    (r : ℂ) ∈ extremalCurve m β ↔ r ^ 2 + β.re = 0 := by
  simp [extremalCurve, ← Complex.ofReal_pow, Complex.norm_real, abs_of_pos hr,
    pow_ne_zero m (ne_of_gt hr)]

lemma sphericalFamily_ne_univ {m : ℕ} (hm : 0 < m) {β : ℂ} (hb : β ≠ star β) :
    sphericalFamily m β ≠ Set.univ := by
  intro he
  have h1 : (((1 : ℝ) : ℂ) : Sphere) ∈ sphericalFamily m β := by rw [he]; trivial
  have h2 : (((2 : ℝ) : ℂ) : Sphere) ∈ sphericalFamily m β := by rw [he]; trivial
  rw [finite_mem_sphericalFamily_iff hm hb, positive_real_mem_family_iff m β (by norm_num)] at h1 h2
  norm_num at h1 h2
  linarith

/-- The cleared pullback is nonzero even when the matrix moves infinity.
If it vanished identically, the closed target would contain the complement
of one sphere point, hence the whole sphere, a contradiction. -/
theorem familyMobiusPullback_ne_zero {m : ℕ} (hm : 0 < m) {β : ℂ}
    (hb : β ≠ star β) (g : MobiusMatrix) : familyMobiusPullback m β g ≠ 0 := by
  intro hz
  have hfinite : ∀ z : ℂ, g • (z : Sphere) ∈ sphericalFamily m β := by
    intro z
    apply (sphericalFamily_projective_iff hm hb _).mp
    rw [sphereRealDiagonal_action]
    apply (familyMobiusPullback_projective_iff m β z (star z) g).mpr
    simp [hz]
  have hsub : ({g • (∞ : Sphere)} : Set Sphere)ᶜ ⊆ sphericalFamily m β := by
    intro p hp
    obtain ⟨q, hq⟩ := (MulAction.toPerm g).surjective p
    change g • q = p at hq
    subst p
    cases q using OnePoint.rec with
    | infty => exact (hp rfl).elim
    | coe z => exact hfinite z
  have hdense : Dense (({g • (∞ : Sphere)} : Set Sphere)ᶜ) := dense_compl_singleton _
  apply sphericalFamily_ne_univ hm hb
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← hdense.closure_eq]
  exact closure_minimal hsub isClosed_closure

/-- Arbitrary Möbius inclusion of the actual spherical loci gives a nonzero
scalar polynomial identity. No pair preservation or normal map form is assumed. -/
theorem family_mobius_proportional {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) :
    ∃ c : ℂ, c ≠ 0 ∧ familyMobiusPullback m β g = C c * familyPolynomial m α :=
  proportional_of_family_dvd hm α (familyMobiusPullback_ne_zero hm hb g)
    (family_dvd_mobiusPullback hm ha hb g hmap) (familyMobiusPullback_degreeOf_le m β g)

#print axioms familyMobiusPullback_degreeOf_le
#print axioms family_degreeOf
#print axioms proportional_of_family_dvd
#print axioms familyMobiusPullback_ne_zero
#print axioms family_mobius_proportional

end CurveSymmetry
