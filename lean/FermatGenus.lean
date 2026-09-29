import FermatSplit

/-!
# The quartic has genus three (R01e-3)

R01e-2 writes a holomorphic differential of `X⁴ + Y⁴ = 2` as a sum of four holomorphic pieces
`aⱼ(x)·yʲ·dx/y³`. At the place over `x = ∞` of R01e-1, with `x = 1/s` and `y = r/s`, the piece is
`rev(aⱼ)(s)·rʲ⁻³·s^(1 − deg aⱼ − j)` up to the regularity factor, where `rev(aⱼ)(0)` is the leading
coefficient and `r` is a unit. As `s` is not a unit, regularity forces `deg aⱼ + j ≤ 1`
(`quarticTerm_natDegree_le`). So `a₂ = a₃ = 0`, `a₁` is constant and `deg a₀ ≤ 1`: every
holomorphic differential is a combination of `dx/y³`, `x·dx/y³` and `dx/y²`
(`quartic_holomorphicSpace_eq_span`). These are independent (R01d), so the genus is three
(`quartic_genus`, and `fermatFunctionField_genus` for the plane curve's function field).
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic
local notation "K₄'" => KummerField 4 fermatDual

lemma dualR_ne_zero : dualR ≠ 0 := by
  intro h
  have h4 : dualR ^ 4 = algebraMap ℂ[X] K₄' fermatDual := kummerRoot_pow 4 fermatDual
  rw [h, zero_pow (by norm_num)] at h4
  have h0 : fermatDual = 0 :=
    kummerField_polynomial_injective (n := 4) (f := fermatDual) (h4.symm.trans (map_zero _).symm)
  have hd := fermatDual_natDegree
  rw [h0, natDegree_zero] at hd
  exact absurd hd (by norm_num)

/-- A polynomial in `x`, read in the chart at infinity: `p(1/s) = rev(p)(s)·s^(−deg p)`. -/
lemma fermatInfinityMap_poly (p : ℂ[X]) :
    fermatInfinityMap (algebraMap ℂ[X] K₄ p) =
      algebraMap ℂ[X] K₄' p.reverse * dualS⁻¹ ^ p.natDegree := by
  let _ : Invertible (dualS⁻¹) := invertibleOfNonzero (inv_ne_zero dualS_ne_zero)
  have hrev : eval₂ (algebraMap ℂ K₄') dualS p.reverse = algebraMap ℂ[X] K₄' p.reverse :=
    eval₂_algebraMap_X p.reverse (IsScalarTower.toAlgHom ℂ ℂ[X] K₄')
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) K₄, fermatInfinityMap_of, ratInv_algebraMap,
    ← aeval_algebraMap_apply, map_inv₀, ← dualS_eq, aeval_def,
    ← eval₂_reverse_mul_pow (algebraMap ℂ K₄') dualS⁻¹ p, invOf_eq_inv, inv_inv, hrev]

/-- **R01e-3, degree bound**: if `p(x)·yʲ·dx/y³` is regular at the place over `x = ∞` and
`p ≠ 0`, then `deg p + j ≤ 1`. In the chart the coefficient is a unit times a power of `s` with
exponent `1 − deg p − j`, and `1/s` is not in the local ring. -/
lemma quarticTerm_natDegree_le {p : ℂ[X]} (hp : p ≠ 0) {j : ℕ}
    (h : quarticTerm p j • KaehlerDifferential.D ℂ K₄ quarticX ∈ regularAt fermatInfinityPlace) :
    p.natDegree + j ≤ 1 := by
  rw [fermat_regularAt_infinity_iff] at h
  by_contra hlt
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ p.natDegree + j by omega)
  have ha0 : algebraMap ℂ[X] K₄' p.reverse ≠ 0 :=
    (map_ne_zero_iff _ (kummerField_polynomial_injective (n := 4) (f := fermatDual))).mpr
      (reverse_eq_zero.not.mpr hp)
  have hainv : (algebraMap ℂ[X] K₄' p.reverse)⁻¹ ∈ dualLocalRing :=
    kummerLocal_poly_inv_mem (n := 4) (f := fermatDual) 0 fermatZeta fermatZeta_pow p.reverse
      (by rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hp)
  obtain ⟨hr, hrinv⟩ := dualR_mem_and_inv_mem
  have hr0 := dualR_ne_zero
  have hs0 := dualS_ne_zero
  have hφ : fermatInfinityMap (quarticTerm p j) * dualS⁻¹ ^ 2 =
      algebraMap ℂ[X] K₄' p.reverse * dualR ^ j * dualR⁻¹ ^ 3 * dualS ^ 3 *
        dualS⁻¹ ^ (p.natDegree + j + 2) := by
    rw [quarticTerm, map_mul, map_mul, map_pow, map_pow, map_inv₀, fermatInfinityMap_poly,
      fermatInfinityMap_root, mul_inv, inv_inv]
    ring
  -- `s³·s^(−(deg p + j + 2)) = s^(−(k + 1))`
  have hsk : dualS ^ 3 * dualS⁻¹ ^ (p.natDegree + j + 2) = dualS⁻¹ ^ (k + 1) := by
    rw [hk, show 2 + k + 2 = 3 + (k + 1) by omega, pow_add, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hs0, one_pow, one_mul]
  -- the unit `rev(p)(s)·rʲ·r⁻³` and its inverse
  have hU : ((algebraMap ℂ[X] K₄' p.reverse)⁻¹ * dualR⁻¹ ^ j * dualR ^ 3) *
      (algebraMap ℂ[X] K₄' p.reverse * dualR ^ j * dualR⁻¹ ^ 3) = 1 := by
    calc _ = ((algebraMap ℂ[X] K₄' p.reverse)⁻¹ * algebraMap ℂ[X] K₄' p.reverse) *
          (dualR⁻¹ * dualR) ^ j * (dualR * dualR⁻¹) ^ 3 := by ring
      _ = 1 := by
        rw [inv_mul_cancel₀ ha0, inv_mul_cancel₀ hr0, mul_inv_cancel₀ hr0]
        simp
  have hk1 : dualS⁻¹ ^ (k + 1) ∈ dualLocalRing := by
    have e : dualS⁻¹ ^ (k + 1) =
        ((algebraMap ℂ[X] K₄' p.reverse)⁻¹ * dualR⁻¹ ^ j * dualR ^ 3) *
          (fermatInfinityMap (quarticTerm p j) * dualS⁻¹ ^ 2) := by
      rw [hφ, mul_assoc _ (dualS ^ 3), hsk, ← mul_assoc, hU, one_mul]
    rw [e]
    exact mul_mem (mul_mem (mul_mem hainv (pow_mem hrinv j)) (pow_mem hr 3)) h
  have hC : dualS⁻¹ = dualS⁻¹ ^ (k + 1) * dualS ^ k := by
    rw [pow_succ', mul_assoc, ← mul_pow, inv_mul_cancel₀ hs0, one_pow, mul_one]
  apply dualS_inv_notMem
  rw [hC]
  exact mul_mem hk1 (pow_mem dualS_mem k)

/-- A holomorphic piece `p(x)·yʲ·dx/y³` has `p = 0` or `deg p + j ≤ 1`. -/
lemma quarticTerm_holo_natDegree {p : ℂ[X]} {j : ℕ} (h : quarticTerm p j ∈ quarticHoloCoeffs) :
    p = 0 ∨ p.natDegree + j ≤ 1 := by
  by_cases hp : p = 0
  · exact Or.inl hp
  · exact Or.inr (quarticTerm_natDegree_le hp
      (mem_holomorphicSpace.mp (mem_quarticHoloCoeffs.mp h) _ fermatInfinityPlace_isComplexPlace))

/-- With `a₀ = c₁x + c₀`, `a₁ = e` and `a₂ = a₃ = 0`, the differential is
`c₀·dx/y³ + c₁·x·dx/y³ + e·dx/y²`. -/
lemma quartic_span_combination (c₀ c₁ e : ℂ) :
    (quarticTerm (C c₁ * X + C c₀) 0 + quarticTerm (C e) 1 + quarticTerm 0 2 +
        quarticTerm 0 3) • KaehlerDifferential.D ℂ K₄ quarticX =
      c₀ • quarticHolo 0 + c₁ • quarticHolo 1 + e • quarticHolo 2 := by
  have hC : ∀ c : ℂ, algebraMap ℂ[X] K₄ (C c) = algebraMap ℂ K₄ c := fun c =>
    (IsScalarTower.algebraMap_apply ℂ ℂ[X] K₄ c).symm
  have hX : algebraMap ℂ[X] K₄ X = quarticX := rfl
  have h0 : quarticHoloNum 0 = 1 := rfl
  have h1 : quarticHoloNum 1 = quarticX := rfl
  have h2 : quarticHoloNum 2 = quarticY := rfl
  simp only [quarticHolo, h0, h1, h2, ← smul_assoc, ← add_smul, Algebra.smul_def]
  congr 1
  simp only [quarticTerm, map_add, map_mul, map_zero, hC, hX]
  ring

/-- **R01e-3**: every holomorphic differential of the quartic is a combination of `dx/y³`,
`x·dx/y³` and `dx/y²`. -/
theorem quartic_holomorphicSpace_le_span :
    holomorphicSpace K₄ ≤ Submodule.span ℂ (Set.range quarticHolo) := by
  intro ω hω
  obtain ⟨a₀, a₁, a₂, a₃, rfl, h₀, h₁, h₂, h₃⟩ := quartic_holomorphic_split hω
  have ha₂ : a₂ = 0 := (quarticTerm_holo_natDegree h₂).resolve_right (by omega)
  have ha₃ : a₃ = 0 := (quarticTerm_holo_natDegree h₃).resolve_right (by omega)
  have ha₁ : a₁ = C (a₁.coeff 0) := by
    refine eq_C_of_natDegree_le_zero ?_
    rcases quarticTerm_holo_natDegree h₁ with h | h
    · rw [h, natDegree_zero]
    · omega
  have ha₀ : a₀ = C (a₀.coeff 1) * X + C (a₀.coeff 0) := by
    refine eq_X_add_C_of_natDegree_le_one ?_
    rcases quarticTerm_holo_natDegree h₀ with h | h
    · rw [h, natDegree_zero]
      exact zero_le_one
    · omega
  rw [ha₂, ha₃, ha₁, ha₀, quartic_span_combination]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))

/-- **R01e-3**: the holomorphic differentials of the quartic are spanned by `dx/y³`, `x·dx/y³`
and `dx/y²`. -/
theorem quartic_holomorphicSpace_eq_span :
    holomorphicSpace K₄ = Submodule.span ℂ (Set.range quarticHolo) :=
  le_antisymm quartic_holomorphicSpace_le_span
    (Submodule.span_le.mpr (Set.range_subset_iff.mpr quarticHolo_mem))

/-- **R01e-3**: the quartic's function field has genus three. -/
theorem quartic_genus : genus K₄ = 3 := by
  rw [genus, quartic_holomorphicSpace_eq_span, finrank_span_eq_card quarticHolo_linearIndependent,
    Fintype.card_fin]

end Quartic

/-- **R01e-3**: the function field of `X⁴ + Y⁴ = 2`, the complexification of `Re(z⁴) = 1`, has
genus three. -/
theorem fermatFunctionField_genus : genus (FermatFunctionField 4) = 3 :=
  (genus_congr fermatFunctionFieldAlgEquiv).trans quartic_genus

#print axioms quarticTerm_natDegree_le
#print axioms quartic_holomorphicSpace_eq_span
#print axioms quartic_genus
#print axioms fermatFunctionField_genus

end CurveSymmetry
