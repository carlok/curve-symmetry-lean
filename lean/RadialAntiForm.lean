import CartesianDescent

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- The coefficients of weight `+m`, `X^(k+m) Y^k`, as a polynomial in `XY`. -/
noncomputable def weightPolynomial (P : BPoly) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ P.support.image (fun s => s 1), Polynomial.monomial k (P.coeff (exponent (k + m) k))

/-- The coefficients of weight `-m`, `X^k Y^(k+m)`, as a polynomial in `XY`. -/
noncomputable def oppositeWeightPolynomial (P : BPoly) (m : ℕ) : Polynomial ℂ :=
  ∑ k ∈ P.support.image (fun s => s 0), Polynomial.monomial k (P.coeff (exponent k (k + m)))

lemma weightPolynomial_coeff (P : BPoly) (m k : ℕ) :
    (weightPolynomial P m).coeff k = P.coeff (exponent (k + m) k) := by
  classical
  simp only [weightPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (Finset.mem_image.mpr ⟨exponent (k + m) k, mem_support_iff.mpr (Ne.symm hc), by simp⟩)

lemma oppositeWeightPolynomial_coeff (P : BPoly) (m k : ℕ) :
    (oppositeWeightPolynomial P m).coeff k = P.coeff (exponent k (k + m)) := by
  classical
  simp only [oppositeWeightPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · by_contra hc
    exact h (Finset.mem_image.mpr ⟨exponent k (k + m), mem_support_iff.mpr (Ne.symm hc), by simp⟩)

lemma X_pow_mul_aeval (m : ℕ) (A : Polynomial ℂ) :
    (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A =
      ∑ k ∈ A.support, monomial (exponent (k + m) k) (A.coeff k) := by
  conv_lhs => rw [A.as_sum_support, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.aeval_monomial, monomial_exponent, MvPolynomial.algebraMap_eq]
  ring

lemma Y_pow_mul_aeval (m : ℕ) (A : Polynomial ℂ) :
    (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A =
      ∑ k ∈ A.support, monomial (exponent k (k + m)) (A.coeff k) := by
  conv_lhs => rw [A.as_sum_support, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Polynomial.aeval_monomial, monomial_exponent, MvPolynomial.algebraMap_eq]
  ring

lemma coeff_sum_weight (A : Polynomial ℂ) (m : ℕ) (s : Exponent) :
    (∑ k ∈ A.support, monomial (exponent (k + m) k) (A.coeff k)).coeff s =
      if s 0 = s 1 + m then A.coeff (s 1) else 0 := by
  classical
  have hc : ∀ k, (exponent (k + m) k = s) ↔ (s 0 = s 1 + m ∧ k = s 1) := by
    intro k
    rw [eq_comm, exponent_eq_iff]
    constructor <;> intro h <;> omega
  simp only [coeff_sum, coeff_monomial, hc]
  by_cases h : s 0 = s 1 + m
  · rw [ite_eq_left h]
    simp only [h, true_and, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact (Polynomial.notMem_support_iff.mp hmem).symm
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun k _ => by simp [h]

lemma coeff_sum_opposite_weight (A : Polynomial ℂ) (m : ℕ) (s : Exponent) :
    (∑ k ∈ A.support, monomial (exponent k (k + m)) (A.coeff k)).coeff s =
      if s 1 = s 0 + m then A.coeff (s 0) else 0 := by
  classical
  have hc : ∀ k, (exponent k (k + m) = s) ↔ (s 1 = s 0 + m ∧ k = s 0) := by
    intro k
    rw [eq_comm, exponent_eq_iff]
    constructor <;> intro h <;> omega
  simp only [coeff_sum, coeff_monomial, hc]
  by_cases h : s 1 = s 0 + m
  · rw [ite_eq_left h]
    simp only [h, true_and, Finset.sum_ite_eq']
    split_ifs with hmem
    · rfl
    · exact (Polynomial.notMem_support_iff.mp hmem).symm
  · rw [ite_eq_right h]
    exact Finset.sum_eq_zero fun k _ => by simp [h]

/-- Equation (5): below degree `2m`, an equation negated by a primitive `2m`th
rotation is `X^m A(XY) + Y^m B(XY)`, with both degrees at most `⌊(d-m)/2⌋`. -/
theorem anti_radial_form {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (2 * m))
    {P : BPoly} (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P) :
    P = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (weightPolynomial P m) +
        (X 1 : BPoly) ^ m *
          Polynomial.aeval ((X 0 : BPoly) * X 1) (oppositeWeightPolynomial P m) ∧
      (weightPolynomial P m).natDegree ≤ (P.totalDegree - m) / 2 ∧
      (oppositeWeightPolynomial P m).natDegree ≤ (P.totalDegree - m) / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [X_pow_mul_aeval, Y_pow_mul_aeval]
    ext s
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_sum_weight, coeff_sum_opposite_weight, weightPolynomial_coeff,
      oppositeWeightPolynomial_coeff]
    by_cases hs : s ∈ P.support
    · rcases anti_support hm hζ hdeg hanti hs with h | h
      · rw [ite_eq_left h, ite_eq_right (by omega), add_zero, ← exponent_eq_iff.mpr ⟨h, rfl⟩]
      · rw [ite_eq_right (by omega), ite_eq_left h, zero_add, ← exponent_eq_iff.mpr ⟨rfl, h⟩]
    · have hc := notMem_support_iff.mp hs
      rw [hc]
      split_ifs with h1 h2 h2
      · omega
      · rw [← exponent_eq_iff.mpr ⟨h1, rfl⟩, hc, add_zero]
      · rw [← exponent_eq_iff.mpr ⟨rfl, h2⟩, hc, zero_add]
      · simp
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [weightPolynomial_coeff]
    by_contra hc
    have hd := support_degree (mem_support_iff.mpr hc)
    simp only [exponent_zero, exponent_one] at hd
    omega
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [oppositeWeightPolynomial_coeff]
    by_contra hc
    have hd := support_degree (mem_support_iff.mpr hc)
    simp only [exponent_zero, exponent_one] at hd
    omega

lemma oppositeWeightPolynomial_eq_map {P : BPoly} (m : ℕ)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    oppositeWeightPolynomial P m = (weightPolynomial P m).map (starRingEnd ℂ) := by
  ext k
  rw [oppositeWeightPolynomial_coeff, Polynomial.coeff_map, weightPolynomial_coeff, hreal]
  rfl

/-- The paper's conclusion from equation (5): with conjugate-symmetric coefficients
the second polynomial is the conjugate of the first, `A` is nonconstant, and
hence `m ≤ d-2`. -/
theorem irreducible_anti_radial_form {m : ℕ} (hm : 2 ≤ m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * m)) {P : BPoly} (hirr : Irreducible P)
    (hdeg : P.totalDegree < 2 * m) (hanti : rotate ζ P = -P)
    (hreal : ∀ a b, P.coeff (exponent b a) = star (P.coeff (exponent a b))) :
    ∃ A : Polynomial ℂ,
      P = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A +
        (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (A.map (starRingEnd ℂ)) ∧
      1 ≤ A.natDegree ∧ A.natDegree ≤ (P.totalDegree - m) / 2 ∧ m + 2 ≤ P.totalDegree := by
  obtain ⟨hform, hA, -⟩ := anti_radial_form (by omega) hζ hdeg hanti
  rw [oppositeWeightPolynomial_eq_map m hreal] at hform
  have h1 : 1 ≤ (weightPolynomial P m).natDegree := by
    by_contra h0
    have hAC := Polynomial.eq_C_of_natDegree_eq_zero (by omega :
      (weightPolynomial P m).natDegree = 0)
    rw [hAC, Polynomial.map_C, Polynomial.aeval_C, Polynomial.aeval_C,
      MvPolynomial.algebraMap_eq] at hform
    apply not_irreducible_pure_powers m hm ((weightPolynomial P m).coeff 0)
      (starRingEnd ℂ ((weightPolynomial P m).coeff 0))
    convert hirr using 1
    conv_rhs => rw [hform]
    ring
  exact ⟨weightPolynomial P m, hform, h1, hA, by omega⟩

/-- A complexified real Cartesian equation has conjugate-symmetric coefficients. -/
lemma complexifyReal_conjugate_coeff (f : RPoly) (a b : ℕ) :
    (complexifyReal f).coeff (exponent b a) = star ((complexifyReal f).coeff (exponent a b)) := by
  have hc : cartesianize (conjugateSwap (complexifyReal f)) =
      cartesianize (complexifyReal f) := by
    rw [← cartesianize_conjugateSwap, complexifyReal, cartesianize_complexify]
    ext s
    simp [MvPolynomial.coeff_map]
  have hfix : conjugateSwap (complexifyReal f) = complexifyReal f := by
    simpa [complexify_cartesianize] using congrArg complexify hc
  rw [← coeff_conjugateSwap, hfix]

/-- S07 for the paper's real Cartesian curve: a rotation of order `N` greater
than the degree forces `N=2m`, the sign `-1`, equation (5) with a nonconstant
`A` of degree at most `⌊(d-m)/2⌋`, and `m ≤ d-2`. -/
theorem paper_high_order_radial_form {f : RPoly} (hf : GeometricallyIrreducible f)
    (hd : 2 ≤ f.totalDegree) (hinf : (cartesianLocus f).Infinite)
    (hnc : ¬ ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧ cartesianLocus f = Metric.sphere c R)
    {N : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hN : f.totalDegree < N)
    (hsym : ∀ z ∈ cartesianLocus f, ζ * z ∈ cartesianLocus f) :
    ∃ m : ℕ, N = 2 * m ∧ rotate ζ (complexifyReal f) = -complexifyReal f ∧
      ∃ A : Polynomial ℂ,
        complexifyReal f = (X 0 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) A +
          (X 1 : BPoly) ^ m * Polynomial.aeval ((X 0 : BPoly) * X 1) (A.map (starRingEnd ℂ)) ∧
        1 ≤ A.natDegree ∧ A.natDegree ≤ (f.totalDegree - m) / 2 ∧ m + 2 ≤ f.totalDegree := by
  have hirr := complexifyReal_irreducible hf
  have hPdeg := complexifyReal_degree f
  have hPinf : (realLocus (complexifyReal f)).Infinite := by rwa [complexifyReal_locus]
  have hsymP : ∀ z ∈ realLocus (complexifyReal f), ζ * z ∈ realLocus (complexifyReal f) := by
    rw [complexifyReal_locus]
    exact hsym
  rcases rotation_sign_of_realLocus hirr hPinf (hζ.norm'_eq_one (by omega)) hsymP with
    hfix | hanti
  · exfalso
    have hform := irreducible_radial_form hirr
      (fun _ hs => fixed_support hζ (by omega) hfix hs)
    obtain ⟨R, hR, he⟩ := radial_realLocus_is_circle hPinf hform
    exact hnc ⟨0, R, hR, by rw [← complexifyReal_locus]; exact he⟩
  · obtain ⟨m, hm⟩ := anti_even_order hζ hirr.ne_zero hanti
    have hN2 : N = 2 * m := by omega
    have hζ' : IsPrimitiveRoot ζ (2 * m) := hN2 ▸ hζ
    obtain ⟨A, hform, h1, hA, hgap⟩ := irreducible_anti_radial_form (by omega) hζ' hirr
      (by omega) hanti (complexifyReal_conjugate_coeff f)
    exact ⟨m, hN2, hanti, A, hform, h1, hPdeg ▸ hA, hPdeg ▸ hgap⟩

#print axioms anti_radial_form
#print axioms irreducible_anti_radial_form
#print axioms complexifyReal_conjugate_coeff
#print axioms paper_high_order_radial_form

end CurveSymmetry
