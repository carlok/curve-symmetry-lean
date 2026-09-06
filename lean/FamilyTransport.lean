import FamilyCharts

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

lemma fourTermForm_monomial (m : ℕ) (a b c d : ℂ) :
    fourTermForm m a b c d = monomial (exponent m 0) a + monomial (exponent 0 m) b +
      monomial (exponent (m + 1) 1) c + monomial (exponent 1 (m + 1)) d := by
  simp only [fourTermForm, binaryForm, monomial_exponent, pow_zero, pow_succ, mul_one]
  ring

lemma fourTermForm_coefficients {m : ℕ} (hm : 0 < m) (a b c d : ℂ) :
    (fourTermForm m a b c d).coeff (exponent m 0) = a ∧
      (fourTermForm m a b c d).coeff (exponent 0 m) = b ∧
      (fourTermForm m a b c d).coeff (exponent (m + 1) 1) = c ∧
      (fourTermForm m a b c d).coeff (exponent 1 (m + 1)) = d := by
  rw [fourTermForm_monomial]
  simp [coeff_monomial, exponent_eq_iff, hm.ne']

lemma fourTermForm_proportional_iff {m : ℕ} (hm : 0 < m) (a b c d A B C' D k : ℂ) :
    fourTermForm m a b c d = C k * fourTermForm m A B C' D ↔
      a = k * A ∧ b = k * B ∧ c = k * C' ∧ d = k * D := by
  constructor
  · intro h
    have h0 := congrArg (coeff (exponent m 0)) h
    have h1 := congrArg (coeff (exponent 0 m)) h
    have h2 := congrArg (coeff (exponent (m + 1) 1)) h
    have h3 := congrArg (coeff (exponent 1 (m + 1))) h
    obtain ⟨ha, hb, hc, hd⟩ := fourTermForm_coefficients hm a b c d
    obtain ⟨hA, hB, hC, hD⟩ := fourTermForm_coefficients hm A B C' D
    rw [ha, coeff_C_mul, hA] at h0
    rw [hb, coeff_C_mul, hB] at h1
    rw [hc, coeff_C_mul, hC] at h2
    rw [hd, coeff_C_mul, hD] at h3
    exact ⟨h0, h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp only [fourTermForm, binaryForm, map_mul]
    ring

lemma dilate_family_fourTerm (m : ℕ) (β c : ℂ) :
    dilate c (familyPolynomial m β) = fourTermForm m (c ^ m * β)
      (star c ^ m * star β) (c ^ m * (c * star c)) (star c ^ m * (c * star c)) := by
  simp only [familyPolynomial, map_add, map_mul, map_pow]
  have h0 : dilate c (X 0) = C c * X 0 := by simp [dilate]
  have h1 : dilate c (X 1) = C (star c) * X 1 := by simp [dilate]
  have hC : ∀ a : ℂ, dilate c (C a) = C a := by intro a; simp [dilate]
  rw [h0, h1, hC, hC]
  simp only [fourTermForm, binaryForm, mul_pow, map_pow, map_mul]
  ring

noncomputable def inversionFamily (m : ℕ) (β c : ℂ) : BPoly :=
  fourTermForm m (star c ^ m * (c * star c)) (c ^ m * (c * star c))
    (star c ^ m * star β) (c ^ m * β)

/-- This is the actual denominator-cleared pullback by `(X,Y) ↦ (c/X,conj(c)/Y)`. -/
lemma inversionFamily_eval (m : ℕ) (β c : ℂ) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    planeEval x y (inversionFamily m β c) =
      (x * y) ^ (m + 1) * planeEval (c / x) (star c / y) (familyPolynomial m β) := by
  rw [inversionFamily, family_fourTerm, fourTermForm_eval, fourTermForm_eval]
  simp only [mul_pow, pow_succ, div_pow, one_mul]
  field_simp
  ring

lemma norm_one_of_mul_star_norm_one {c : ℂ} (h : ‖c * star c‖ = 1) : ‖c‖ = 1 := by
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by decide : 2 ≠ 0)).mp
  simpa [norm_mul, norm_star, pow_two] using h

/-- Normalized parameters cannot change under a direct similarity. -/
theorem family_dilation_parameter {m : ℕ} (hm : 0 < m) {α β c k : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hc : c ≠ 0)
    (he : dilate c (familyPolynomial m β) = C k * familyPolynomial m α) :
    ‖c‖ = 1 ∧ β = α := by
  rw [dilate_family_fourTerm, family_fourTerm] at he
  obtain ⟨hlow, _, hhigh, _⟩ :=
    (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
  rw [mul_one] at hhigh
  have hp : β = (c * star c) * α := by
    apply mul_left_cancel₀ (pow_ne_zero m hc)
    rw [hlow, ← hhigh]
    ring
  have hn := congrArg norm hp
  rw [hβ, norm_mul, hα, mul_one] at hn
  have hcn := norm_one_of_mul_star_norm_one hn.symm
  rw [mul_star_eq_one_of_norm hcn, one_mul] at hp
  exact ⟨hcn, hp⟩

/-- The same normalized parameter is forced by an inversion-type pullback. -/
theorem family_inversion_parameter {m : ℕ} (hm : 0 < m) {α β c k : ℂ}
    (hα : ‖α‖ = 1) (hβ : ‖β‖ = 1) (hc : c ≠ 0)
    (he : inversionFamily m β c = C k * familyPolynomial m α) :
    ‖c‖ = 1 ∧ β = α := by
  rw [inversionFamily, family_fourTerm] at he
  obtain ⟨hlow, _, hhigh, _⟩ :=
    (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
  rw [mul_one] at hhigh
  have hp : c * star c = star β * α := by
    apply mul_left_cancel₀ (pow_ne_zero m (star_ne_zero.mpr hc))
    rw [hlow, ← hhigh]
    ring
  have hn := congrArg norm hp
  rw [norm_mul (star β), norm_star, hβ, hα, one_mul] at hn
  have hcn := norm_one_of_mul_star_norm_one hn
  refine ⟨hcn, ?_⟩
  have hβc := mul_star_eq_one_of_norm hβ
  rw [mul_star_eq_one_of_norm hcn] at hp
  calc
    β = β * (star β * α) := by rw [← hp, mul_one]
    _ = α := by rw [← mul_assoc, hβc, one_mul]

lemma unit_power_product (m : ℕ) {c : ℂ} (hc : ‖c‖ = 1) : c ^ m * star c ^ m = 1 := by
  rw [← mul_pow, mul_star_eq_one_of_norm hc, one_pow]

theorem family_dilation_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∃ k : ℂ, dilate c (familyPolynomial m α) = C k * familyPolynomial m α) ↔
      c ^ (2 * m) = 1 := by
  constructor
  · rintro ⟨k, he⟩
    have hn := (family_dilation_parameter hm hα hα hc he).1
    rw [dilate_family_fourTerm, family_fourTerm] at he
    obtain ⟨_, _, h0, h1⟩ := (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
    rw [mul_star_eq_one_of_norm hn, mul_one, mul_one] at h0 h1
    have hp : c ^ m = star c ^ m := h0.trans h1.symm
    calc
      c ^ (2 * m) = c ^ m * c ^ m := by rw [two_mul, pow_add]
      _ = c ^ m * star c ^ m := congrArg (fun w => c ^ m * w) hp
      _ = 1 := unit_power_product m hn
  · intro hroot
    have hn : ‖c‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega : 2 * m ≠ 0)).mp
      simpa using congrArg norm hroot
    have hp : c ^ m = star c ^ m := by
      apply mul_left_cancel₀ (pow_ne_zero m hc)
      rw [unit_power_product m hn, ← pow_add, ← two_mul, hroot]
    refine ⟨c ^ m, ?_⟩
    rw [dilate_family_fourTerm, family_fourTerm, fourTermForm_proportional_iff hm,
      mul_star_eq_one_of_norm hn]
    simp [hp]

theorem family_inversion_filter {m : ℕ} (hm : 0 < m) {α c : ℂ}
    (hα : ‖α‖ = 1) (hc : c ≠ 0) :
    (∃ k : ℂ, inversionFamily m α c = C k * familyPolynomial m α) ↔
      c ^ (2 * m) = star α ^ 2 := by
  constructor
  · rintro ⟨k, he⟩
    have hn := (family_inversion_parameter hm hα hα hc he).1
    rw [inversionFamily, family_fourTerm] at he
    obtain ⟨_, hlow, hhigh, _⟩ := (fourTermForm_proportional_iff hm _ _ _ _ _ _ _ _ _).mp he
    rw [mul_star_eq_one_of_norm hn, mul_one] at hlow
    rw [mul_one] at hhigh
    have hp : c ^ m = star c ^ m * star α ^ 2 := by
      rw [hlow, ← hhigh]
      ring
    calc
      c ^ (2 * m) = c ^ m * c ^ m := by rw [two_mul, pow_add]
      _ = c ^ m * (star c ^ m * star α ^ 2) := congrArg (fun w => c ^ m * w) hp
      _ = star α ^ 2 := by rw [← mul_assoc, unit_power_product m hn, one_mul]
  · intro hroot
    have hn : ‖c‖ = 1 := by
      apply (pow_eq_one_iff_of_nonneg (norm_nonneg c) (by omega : 2 * m ≠ 0)).mp
      simpa [norm_pow, norm_star, hα] using congrArg norm hroot
    have hp : c ^ m = star c ^ m * star α ^ 2 := by
      apply mul_left_cancel₀ (pow_ne_zero m hc)
      rw [← mul_assoc, unit_power_product m hn, one_mul, ← pow_add, ← two_mul, hroot]
    have ha := mul_star_eq_one_of_norm hα
    refine ⟨star c ^ m * star α, ?_⟩
    rw [inversionFamily, family_fourTerm, fourTermForm_proportional_iff hm,
      mul_star_eq_one_of_norm hn]
    refine ⟨?_, ?_, by ring, ?_⟩
    · linear_combination -(star c ^ m) * ha
    · simpa only [mul_one, mul_assoc, pow_two] using hp
    · rw [hp]
      linear_combination star c ^ m * star α * ha

/-- Exchanging the two complexified coordinates conjugates the family parameter. -/
lemma family_swap_eval (m : ℕ) (β x y : ℂ) :
    planeEval y x (familyPolynomial m β) = planeEval x y (familyPolynomial m (star β)) := by
  rw [family_fourTerm, family_fourTerm, fourTermForm_eval, fourTermForm_eval]
  simp only [star_star, one_mul]
  ring

theorem family_no_conjugated_dilation {m : ℕ} (hm : 0 < m) {α c k : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0) :
    dilate c (familyPolynomial m (star α)) ≠ C k * familyPolynomial m α := by
  intro he
  have hp := (family_dilation_parameter hm hα (by simpa using hα) hc he).2
  exact ha hp.symm

theorem family_no_conjugated_inversion {m : ℕ} (hm : 0 < m) {α c k : ℂ}
    (hα : ‖α‖ = 1) (ha : α ≠ star α) (hc : c ≠ 0) :
    inversionFamily m (star α) c ≠ C k * familyPolynomial m α := by
  intro he
  have hp := (family_inversion_parameter hm hα (by simpa using hα) hc he).2
  exact ha hp.symm

#print axioms fourTermForm_proportional_iff
#print axioms inversionFamily_eval
#print axioms family_dilation_parameter
#print axioms family_inversion_parameter
#print axioms family_dilation_filter
#print axioms family_inversion_filter
#print axioms family_no_conjugated_dilation
#print axioms family_no_conjugated_inversion

end CurveSymmetry
