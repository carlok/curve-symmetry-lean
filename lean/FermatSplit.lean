import FermatInfinity

/-!
# Holomorphic differentials of the quartic split into four pieces (R01e-2)

Let `K = KummerField 4 f`, `f = 2 − x⁴`, the function field of `X⁴ + Y⁴ = 2`. Every
differential is `F·dx` (R01c-1).

* Affine step: if `F·dx` is holomorphic, then `F·y³` lies in the local ring at every affine
  point, by R01c-2b's criteria (`F` there where `f(a) ≠ 0`, `F·y³` where `f(a) = 0`), so it comes
  from the coordinate ring `ℂ[x][y]/(y⁴ − f)` (`quartic_mul_y3_mem_range`). Reducing modulo
  `y⁴ − f` gives `F·y³ = a₀(x) + a₁(x)·y + a₂(x)·y² + a₃(x)·y³`.
* The automorphism `σ : y ↦ i·y` of `K` over `ℂ(x)` (`quarticRot`) fixes `x`, so it carries
  holomorphic `F·dx` to holomorphic `σ(F)·dx` (R01a's invariance). The piece
  `aⱼ(x)·yʲ/y³` is an eigenvector with eigenvalue `iʲ⁺¹`, and each piece is a combination of
  `F`, `σF`, `σ²F`, `σ³F` with coefficients `±1`, `±i` (`quartic_isotypic_mem`).

So each `aⱼ(x)·yʲ·dx/y³` is holomorphic on its own (`quartic_holomorphic_split`). R01e-3 bounds
the degree of `aⱼ` at one place over `x = ∞`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section Reduction

/-- An element of the Kummer coordinate ring given by a polynomial of degree less than `n` in `Y`
is `Σ gⱼ(x)·yʲ` in the function field. -/
lemma kummerRingMap_mk_eq_sum {n : ℕ} {f : ℂ[X]} (g : ℂ[X][X]) (hg : g.natDegree < n) :
    kummerRingMap n f (AdjoinRoot.mk (kummerPoly n f) g) =
      ∑ j ∈ Finset.range n, algebraMap ℂ[X] (KummerField n f) (g.coeff j) *
        AdjoinRoot.root (kummerRat n f) ^ j := by
  rw [← AdjoinRoot.aeval_eq, ← Polynomial.aeval_algHom_apply, kummerRingMap_root, aeval_def,
    eval₂_eq_sum_range' _ hg]

/-- Every element of the Kummer coordinate ring is `Σ_{j<n} aⱼ(x)·yʲ` in the function field. -/
lemma kummer_exists_sum {n : ℕ} {f : ℂ[X]} (hn : n ≠ 0) (r : KummerRing n f) :
    ∃ a : ℕ → ℂ[X], kummerRingMap n f r =
      ∑ j ∈ Finset.range n, algebraMap ℂ[X] (KummerField n f) (a j) *
        AdjoinRoot.root (kummerRat n f) ^ j := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective r
  have hm := kummerPoly_monic n f hn
  have hdeg : (kummerPoly n f).natDegree = n := by
    show (X ^ n - C f).natDegree = n
    exact natDegree_X_pow_sub_C
  have hne : kummerPoly n f ≠ 1 := fun h => hn (by rw [← hdeg, h, natDegree_one])
  have hmk : AdjoinRoot.mk (kummerPoly n f) g =
      AdjoinRoot.mk (kummerPoly n f) (g %ₘ kummerPoly n f) :=
    (AdjoinRoot.mk_leftInverse hm (AdjoinRoot.mk _ g)).symm.trans
      (congrArg (AdjoinRoot.mk _) (AdjoinRoot.modByMonicHom_mk hm g))
  refine ⟨fun j => (g %ₘ kummerPoly n f).coeff j, ?_⟩
  rw [hmk]
  refine kummerRingMap_mk_eq_sum _ ?_
  have := natDegree_modByMonic_lt g hm hne
  rwa [hdeg] at this

end Reduction

section Quartic

local notation "K₄" => KummerField 4 fermatQuartic

/-- **R01e-2, affine step**: if `F·dx` is holomorphic, `F·y³` comes from the coordinate ring. -/
lemma quartic_mul_y3_mem_range {F : K₄}
    (hF : F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄) :
    ∃ r : KummerRing 4 fermatQuartic, kummerRingMap 4 fermatQuartic r = F * quarticY ^ 3 := by
  refine kummer_mem_range_of_forall_local (n := 4) (f := fermatQuartic) _ fun a b hb => ?_
  have hreg := mem_holomorphicSpace.mp hF _
    (kummerPlace_isComplexPlace (n := 4) (f := fermatQuartic) a b hb)
  by_cases hfa : fermatQuartic.eval a = 0
  · exact (mem_kummerPlace_iff a b hb _).mp
      ((kummer_regularAt_ramified (n := 4) (f := fermatQuartic) a b hb hfa F).mp hreg)
  · have hF' := (mem_kummerPlace_iff a b hb _).mp
      ((kummer_regularAt_unramified (n := 4) (f := fermatQuartic) a b hb hfa F).mp hreg)
    exact mul_mem hF' (pow_mem (kummerLocal_root_mem (n := 4) (f := fermatQuartic) a b hb) 3)

/-- `i` in the quartic's function field. -/
noncomputable abbrev quarticI : K₄ := algebraMap ℂ K₄ Complex.I

lemma quarticI_sq : quarticI ^ 2 = -1 := by
  rw [quarticI, ← map_pow, Complex.I_sq, map_neg, map_one]

lemma quarticI_pow_four : quarticI ^ 4 = 1 := by
  linear_combination (quarticI ^ 2 - 1) * quarticI_sq

/-- `y ↦ i·y` over `ℂ(x)`: well defined because `(i·y)⁴ = y⁴ = f(x)`. -/
noncomputable def quarticRotHom : K₄ →ₐ[RatFunc ℂ] K₄ :=
  AdjoinRoot.liftAlgHom (kummerRat 4 fermatQuartic) (Algebra.ofId (RatFunc ℂ) K₄)
    (quarticI * quarticY) (by
      show eval₂ _ _ (X ^ 4 - C (algebraMap ℂ[X] (RatFunc ℂ) fermatQuartic)) = 0
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, quarticI_pow_four, one_mul, quarticY,
        kummerRoot_pow, AlgHom.coe_toRingHom, Algebra.ofId_apply,
        ← IsScalarTower.algebraMap_apply, sub_self])

/-- **R01e-2**: the automorphism `σ : y ↦ i·y` of the quartic's function field, fixing
`ℂ(x)`. -/
noncomputable def quarticRot : K₄ ≃ₐ[ℂ] K₄ :=
  (AlgEquiv.ofBijective quarticRotHom (AlgHom.bijective quarticRotHom)).restrictScalars ℂ

lemma quarticRot_apply (z : K₄) : quarticRot z = quarticRotHom z :=
  rfl

lemma quarticRot_ratFunc (q : RatFunc ℂ) :
    quarticRot (algebraMap (RatFunc ℂ) K₄ q) = algebraMap (RatFunc ℂ) K₄ q :=
  quarticRotHom.commutes q

lemma quarticRot_poly (p : ℂ[X]) :
    quarticRot (algebraMap ℂ[X] K₄ p) = algebraMap ℂ[X] K₄ p := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) K₄, quarticRot_ratFunc]

lemma quarticRot_x : quarticRot quarticX = quarticX := by
  show quarticRot (kummerX 4 fermatQuartic) = kummerX 4 fermatQuartic
  rw [kummerX_eq, quarticRot_ratFunc]

lemma quarticRot_y : quarticRot quarticY = quarticI * quarticY := by
  rw [quarticRot_apply]
  exact AdjoinRoot.liftAlgHom_root (kummerRat 4 fermatQuartic) _ _ _

lemma quarticRot_I : quarticRot quarticI = quarticI :=
  quarticRot.commutes _

/-- `σ` carries holomorphic `F·dx` to holomorphic `σ(F)·dx`, since `σ(x) = x`. -/
lemma quarticRot_mem {F : K₄}
    (hF : F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄) :
    quarticRot F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ := by
  have h := kaehlerTransport_mem_holomorphicSpace quarticRot hF
  rwa [kaehlerTransport_smul, kaehlerTransport_D, quarticRot_x] at h

/-- The coefficients `F` with `F·dx` holomorphic, a `ℂ`-subspace of the function field. -/
noncomputable def quarticHoloCoeffs : Submodule ℂ K₄ :=
  (holomorphicSpace K₄).comap
    ((LinearMap.toSpanSingleton K₄ _ (KaehlerDifferential.D ℂ K₄ quarticX)).restrictScalars ℂ)

lemma mem_quarticHoloCoeffs {F : K₄} :
    F ∈ quarticHoloCoeffs ↔ F • KaehlerDifferential.D ℂ K₄ quarticX ∈ holomorphicSpace K₄ :=
  Iff.rfl

/-- The piece `p(x)·yʲ/y³`. -/
noncomputable def quarticTerm (p : ℂ[X]) (j : ℕ) : K₄ :=
  algebraMap ℂ[X] K₄ p * quarticY ^ j * quarticY⁻¹ ^ 3

/-- `σ(p(x)·yʲ/y³) = iʲ⁺¹·p(x)·yʲ/y³`. -/
lemma quarticRot_term (p : ℂ[X]) (j : ℕ) :
    quarticRot (quarticTerm p j) = quarticI ^ (j + 1) * quarticTerm p j := by
  have hI := quarticI_sq
  have hinv : quarticI⁻¹ = -quarticI :=
    inv_eq_of_mul_eq_one_right (by linear_combination -hI)
  rw [quarticTerm, map_mul, map_mul, map_pow, map_pow, map_inv₀, quarticRot_poly, quarticRot_y,
    mul_inv, hinv]
  linear_combination
    (-(algebraMap ℂ[X] K₄ p * quarticI ^ (j + 1) * quarticY ^ j * quarticY⁻¹ ^ 3)) * hI

lemma quarticRot_term_zero (p : ℂ[X]) :
    quarticRot (quarticTerm p 0) = quarticI * quarticTerm p 0 := by
  rw [quarticRot_term, zero_add, pow_one]

lemma quarticRot_term_one (p : ℂ[X]) : quarticRot (quarticTerm p 1) = -quarticTerm p 1 := by
  rw [quarticRot_term]
  linear_combination quarticTerm p 1 * quarticI_sq

lemma quarticRot_term_two (p : ℂ[X]) :
    quarticRot (quarticTerm p 2) = -(quarticI * quarticTerm p 2) := by
  rw [quarticRot_term]
  linear_combination quarticI * quarticTerm p 2 * quarticI_sq

lemma quarticRot_term_three (p : ℂ[X]) : quarticRot (quarticTerm p 3) = quarticTerm p 3 := by
  rw [quarticRot_term]
  linear_combination (quarticI ^ 2 - 1) * quarticTerm p 3 * quarticI_sq

/-- **R01e-2, isotypic split**: in a `σ`-stable `ℂ`-subspace, the eigencomponents of an element
lie in the subspace. `4·G₃ = F + σF + σ²F + σ³F`, `4·G₁ = F − σF + σ²F − σ³F`,
`4·G₀ = F − i·σF − σ²F + i·σ³F`, `4·G₂ = F + i·σF − σ²F − i·σ³F`. -/
lemma quartic_isotypic_mem {V : Submodule ℂ K₄} (hV : ∀ G ∈ V, quarticRot G ∈ V)
    {G₀ G₁ G₂ G₃ : K₄} (h₀ : quarticRot G₀ = quarticI * G₀) (h₁ : quarticRot G₁ = -G₁)
    (h₂ : quarticRot G₂ = -(quarticI * G₂)) (h₃ : quarticRot G₃ = G₃)
    (hF : G₀ + G₁ + G₂ + G₃ ∈ V) : G₀ ∈ V ∧ G₁ ∈ V ∧ G₂ ∈ V ∧ G₃ ∈ V := by
  have hI := quarticI_sq
  have hIm : ∀ G ∈ V, quarticI * G ∈ V := fun G hG => by
    rw [← Algebra.smul_def]
    exact V.smul_mem _ hG
  have h4 : ∀ G : K₄, 4 * G ∈ V → G ∈ V := fun G hG => by
    have h4G : (4 : K₄) * G = (4 : ℂ) • G := by rw [Algebra.smul_def, map_ofNat]
    rw [h4G] at hG
    have := V.smul_mem (4 : ℂ)⁻¹ hG
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num), one_smul] at this
  have e1 : quarticRot (G₀ + G₁ + G₂ + G₃) = quarticI * G₀ - G₁ - quarticI * G₂ + G₃ := by
    simp only [map_add, h₀, h₁, h₂, h₃]
    ring
  have e2 : quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) = -G₀ + G₁ - G₂ + G₃ := by
    rw [e1]
    simp only [map_add, map_sub, map_mul, quarticRot_I, h₀, h₁, h₂, h₃]
    linear_combination (G₀ + G₂) * hI
  have e3 : quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) =
      -(quarticI * G₀) - G₁ + quarticI * G₂ + G₃ := by
    rw [e2]
    simp only [map_add, map_sub, map_neg, h₀, h₁, h₂, h₃]
    ring
  have m1 := hV _ hF
  have m2 := hV _ m1
  have m3 := hV _ m2
  refine ⟨h4 _ ?_, h4 _ ?_, h4 _ ?_, h4 _ ?_⟩
  · have h : 4 * G₀ = G₀ + G₁ + G₂ + G₃ - quarticI * quarticRot (G₀ + G₁ + G₂ + G₃) -
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) +
        quarticI * quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      linear_combination 2 * (G₀ - G₂) * hI
    rw [h]
    exact add_mem (sub_mem (sub_mem hF (hIm _ m1)) m2) (hIm _ m3)
  · have h : 4 * G₁ = G₀ + G₁ + G₂ + G₃ - quarticRot (G₀ + G₁ + G₂ + G₃) +
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) -
        quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      ring
    rw [h]
    exact sub_mem (add_mem (sub_mem hF m1) m2) m3
  · have h : 4 * G₂ = G₀ + G₁ + G₂ + G₃ + quarticI * quarticRot (G₀ + G₁ + G₂ + G₃) -
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) -
        quarticI * quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      linear_combination 2 * (G₂ - G₀) * hI
    rw [h]
    exact sub_mem (sub_mem (add_mem hF (hIm _ m1)) m2) (hIm _ m3)
  · have h : 4 * G₃ = G₀ + G₁ + G₂ + G₃ + quarticRot (G₀ + G₁ + G₂ + G₃) +
        quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃)) +
        quarticRot (quarticRot (quarticRot (G₀ + G₁ + G₂ + G₃))) := by
      rw [e3, e2, e1]
      ring
    rw [h]
    exact add_mem (add_mem (add_mem hF m1) m2) m3

/-- **R01e-2**: a holomorphic differential of the quartic is
`(a₀(x) + a₁(x)·y + a₂(x)·y² + a₃(x)·y³)·dx/y³`, and each of the four pieces is holomorphic. -/
theorem quartic_holomorphic_split {ω : Ω[K₄⁄ℂ]} (hω : ω ∈ holomorphicSpace K₄) :
    ∃ a₀ a₁ a₂ a₃ : ℂ[X],
      ω = (quarticTerm a₀ 0 + quarticTerm a₁ 1 + quarticTerm a₂ 2 + quarticTerm a₃ 3) •
        KaehlerDifferential.D ℂ K₄ quarticX ∧
      quarticTerm a₀ 0 ∈ quarticHoloCoeffs ∧ quarticTerm a₁ 1 ∈ quarticHoloCoeffs ∧
      quarticTerm a₂ 2 ∈ quarticHoloCoeffs ∧ quarticTerm a₃ 3 ∈ quarticHoloCoeffs := by
  obtain ⟨F, rfl⟩ := kummer_exists_smul_D_x 4 fermatQuartic ω
  obtain ⟨r, hr⟩ := quartic_mul_y3_mem_range hω
  obtain ⟨a, ha⟩ := kummer_exists_sum (n := 4) (f := fermatQuartic) (by norm_num) r
  have h := ha.symm.trans hr
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  have hy3 : quarticY ^ 3 * quarticY⁻¹ ^ 3 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ quarticY_ne_zero, one_pow]
  have hF : F = quarticTerm (a 0) 0 + quarticTerm (a 1) 1 + quarticTerm (a 2) 2 +
      quarticTerm (a 3) 3 := by
    calc F = F * quarticY ^ 3 * quarticY⁻¹ ^ 3 := by rw [mul_assoc, hy3, mul_one]
      _ = _ := by
        rw [← h]
        simp only [quarticTerm]
        ring
  have hmem : F ∈ quarticHoloCoeffs := hω
  rw [hF] at hmem
  obtain ⟨m0, m1, m2, m3⟩ := quartic_isotypic_mem (fun G hG => quarticRot_mem hG)
    (quarticRot_term_zero _) (quarticRot_term_one _) (quarticRot_term_two _)
    (quarticRot_term_three _) hmem
  exact ⟨a 0, a 1, a 2, a 3, by rw [← hF], m0, m1, m2, m3⟩

#print axioms quartic_mul_y3_mem_range
#print axioms quartic_isotypic_mem
#print axioms quartic_holomorphic_split

end Quartic

end CurveSymmetry
