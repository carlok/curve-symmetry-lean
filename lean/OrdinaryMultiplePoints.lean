import BinaryTangentDirections
import FamilyGlobalSingularities
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.MvPolynomial.Ideal

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

/-- The maximal ideal of polynomials vanishing at the complex point `(x,y)`. -/
noncomputable def pointIdeal (x y : ℂ) : Ideal BPoly :=
  Ideal.span {X 0 - C x, X 1 - C y}

/-- The usual algebraic multiplicity of a plane curve equation at a point:
membership in the `n`th, but not the `(n+1)`st, power of the maximal ideal. -/
def HasMultiplicityAt (P : BPoly) (x y : ℂ) (n : ℕ) : Prop :=
  P ∈ pointIdeal x y ^ n ∧ P ∉ pointIdeal x y ^ (n + 1)

theorem hasMultiplicityAt_unique {P : BPoly} {x y : ℂ} {n k : ℕ}
    (hn : HasMultiplicityAt P x y n) (hk : HasMultiplicityAt P x y k) : n = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact hn.2 (Ideal.pow_le_pow_right (by omega) hk.1)
  · exact hk.2 (Ideal.pow_le_pow_right (by omega) hn.1)

lemma pointIdeal_origin : pointIdeal 0 0 = idealOfVars (Fin 2) ℂ := by
  have hr : Set.range (X : Fin 2 → BPoly) = {X 0, X 1} := by
    ext p
    simp [Fin.exists_fin_two, eq_comm]
  simp [pointIdeal, idealOfVars, hr]

/-- Membership in the point ideal is exactly vanishing at the point. -/
theorem mem_pointIdeal_iff (P : BPoly) (x y : ℂ) :
    P ∈ pointIdeal x y ↔ planeEval x y P = 0 := by
  constructor
  · intro hP
    have hle : pointIdeal x y ≤ RingHom.ker (planeEval x y) := by
      rw [pointIdeal, Ideal.span_le]
      rintro _ (rfl | rfl) <;> simp
    exact hle hP
  · intro hP
    have key : ∀ Q : BPoly, Q - C (planeEval x y Q) ∈ pointIdeal x y := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq =>
          simpa [map_add, C_add, add_sub_add_comm] using Ideal.add_mem _ hp hq
      | mul_X p i hp =>
          have hi : X i - C (planeEval x y (X i)) ∈ pointIdeal x y := by
            fin_cases i
            · exact Ideal.subset_span (by simp)
            · exact Ideal.subset_span (by simp)
          have he : p * X i - C (planeEval x y (p * X i)) =
              (p - C (planeEval x y p)) * X i +
                C (planeEval x y p) * (X i - C (planeEval x y (X i))) := by
            simp only [map_mul]
            ring
          rw [he]
          exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hi)
    simpa [hP] using key P

/-- The polynomials whose value and both formal partial derivatives vanish at a
point form an ideal. -/
noncomputable def jacobianIdeal (x y : ℂ) : Ideal BPoly where
  carrier := {P | JacobianSingular P x y}
  add_mem' := by
    rintro P Q ⟨hP, hP0, hP1⟩ ⟨hQ, hQ0, hQ1⟩
    exact ⟨by simp [hP, hQ], by simp [hP0, hQ0], by simp [hP1, hQ1]⟩
  zero_mem' := by simp [JacobianSingular]
  smul_mem' := by
    rintro c P ⟨hP, hP0, hP1⟩
    exact ⟨by simp [hP], by simp [hP, hP0], by simp [hP, hP1]⟩

/-- A second-order zero is a Jacobian singularity. -/
theorem jacobianSingular_of_mem_sq {P : BPoly} {x y : ℂ}
    (hP : P ∈ pointIdeal x y ^ 2) : JacobianSingular P x y := by
  have hle : pointIdeal x y ^ 2 ≤ jacobianIdeal x y := by
    rw [sq, Ideal.mul_le]
    intro r hr s hs
    have hr0 := (mem_pointIdeal_iff r x y).mp hr
    have hs0 := (mem_pointIdeal_iff s x y).mp hs
    exact ⟨by simp [hr0, hs0], by simp [hr0, hs0], by simp [hr0, hs0]⟩
  exact hle hP

/-- A nonsingular zero of a plane equation has multiplicity exactly one. -/
theorem hasMultiplicityAt_one {P : BPoly} {x y : ℂ} (hz : planeEval x y P = 0)
    (hs : ¬ JacobianSingular P x y) : HasMultiplicityAt P x y 1 :=
  ⟨by simpa using (mem_pointIdeal_iff P x y).mpr hz,
    fun h => hs (jacobianSingular_of_mem_sq h)⟩

/-- An ordinary `n`-fold point at the origin: multiplicity `n`, and the tangent
cone, the degree-`n` component, is a nonzero multiple of `n` pairwise
nonproportional nonzero linear forms. -/
def OrdinaryAtOrigin (P : BPoly) (n : ℕ) : Prop :=
  HasMultiplicityAt P 0 0 n ∧
    ∃ (c : ℂ) (ℓ : Fin n → Fin 2 → ℂ), c ≠ 0 ∧ (∀ i, ℓ i ≠ 0) ∧
      (∀ i j, i ≠ j → ℓ i 0 * ℓ j 1 - ℓ i 1 * ℓ j 0 ≠ 0) ∧
      homogeneousComponent n P = C c * ∏ i, (C (ℓ i 0) * X 0 + C (ℓ i 1) * X 1)

lemma homogeneousComponent_eq_zero_of_mem_pow {P : BPoly} {n : ℕ}
    (hP : P ∈ idealOfVars (Fin 2) ℂ ^ (n + 1)) : homogeneousComponent n P = 0 := by
  ext d
  rw [coeff_homogeneousComponent, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with hd
  · exact (mem_pow_idealOfVars_iff' (n + 1) P).mp hP d (by omega)
  · rfl

/-- The binary tangent form splits into `m` explicit distinct linear factors. -/
theorem binaryForm_eq_prod {m : ℕ} (hm : 0 < m) {a b w ζ : ℂ} (ha : a ≠ 0)
    (hζ : IsPrimitiveRoot ζ m) (hw : w ^ m = -b / a) :
    binaryForm m a b =
      C a * ∏ i : Fin m, (C (1 : ℂ) * X 0 + C (-(ζ ^ (i : ℕ) * w)) * X 1) := by
  have hpoly := _root_.X_pow_sub_C_eq_prod hζ hm hw
  apply MvPolynomial.funext
  intro v
  have hprod : ∀ t : ℂ, t ^ m - (-b / a) = ∏ i ∈ Finset.range m, (t - ζ ^ i * w) := by
    intro t
    simpa [Polynomial.eval_prod] using congrArg (Polynomial.eval t) hpoly
  simp only [binaryForm, map_add, map_mul, map_pow, eval_C, eval_X, map_prod, map_neg,
    one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => v 0 + -(ζ ^ i * w) * v 1) m]
  by_cases hv : v 1 = 0
  · simp [hv, hm.ne']
  · have hs : ∏ i ∈ Finset.range m, (v 0 + -(ζ ^ i * w) * v 1) =
        v 1 ^ m * ∏ i ∈ Finset.range m, (v 0 / v 1 - ζ ^ i * w) := by
      rw [← Finset.card_range m, ← Finset.prod_const, Finset.card_range,
        ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      field_simp
      ring
    have hab : a * (-b / a) = -b := by field_simp
    rw [hs, ← hprod, div_pow, mul_sub, mul_div_cancel₀ _ (pow_ne_zero m hv)]
    linear_combination (v 1 ^ m) * hab

/-- The four-term chart equation has an ordinary `m`-fold point at its origin. -/
theorem fourTermForm_ordinary {m : ℕ} (hm : 0 < m) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (c d : ℂ) : OrdinaryAtOrigin (fourTermForm m a b c d) m := by
  obtain ⟨hlow, hcomp, hnz, _⟩ := fourTermForm_tangent_data hm ha hb c d
  have hbin (a b : ℂ) : binaryForm m a b ∈ idealOfVars (Fin 2) ℂ ^ m := by
    have hX (i : Fin 2) : (X i : BPoly) ^ m ∈ idealOfVars (Fin 2) ℂ ^ m :=
      Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) m
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hX 0)) (Ideal.mul_mem_left _ _ (hX 1))
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pointIdeal_origin]
    exact Ideal.add_mem _ (hbin a b) (Ideal.mul_mem_left _ _ (hbin c d))
  · rw [pointIdeal_origin]
    intro hmem
    exact hnz (hcomp ▸ homogeneousComponent_eq_zero_of_mem_pow hmem)
  · let ζ := Complex.exp (2 * Real.pi * Complex.I / m)
    have hζ : IsPrimitiveRoot ζ m := Complex.isPrimitiveRoot_exp m hm.ne'
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-b / a) hm
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact div_ne_zero (neg_ne_zero.mpr hb) ha (by simpa [hm.ne'] using hw.symm)
    refine ⟨a, fun i => ![1, -(ζ ^ (i : ℕ) * w)], ha, fun i => by simp, ?_, ?_⟩
    · intro i j hij
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      have hpow : ζ ^ (i : ℕ) ≠ ζ ^ (j : ℕ) := by
        intro he
        exact hij (Fin.ext (hζ.pow_inj i.isLt j.isLt he))
      have hsub : ζ ^ (i : ℕ) - ζ ^ (j : ℕ) ≠ 0 := sub_ne_zero.mpr hpow
      intro hz
      apply mul_ne_zero hsub hw0
      linear_combination hz
    · rw [hcomp, binaryForm_eq_prod hm ha hζ hw]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

lemma projective_mk_one_ne_origin (x : ℂ) :
    Projectivization.mk ℂ ![1, x] (by simp) ≠ sphereProjectiveEquiv ((0 : ℂ) : Sphere) := by
  intro h
  rw [sphereProjectiveEquiv_finite, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h := congrFun ha 0
  simp at h

lemma projective_mk_one_ne_infinity (y : ℂ) :
    Projectivization.mk ℂ ![y, 1] (by simp) ≠ sphereProjectiveEquiv (OnePoint.infty : Sphere) := by
  intro h
  rw [sphereProjectiveEquiv_infinity, Projectivization.mk_eq_mk_iff] at h
  obtain ⟨a, ha⟩ := h
  have h := congrFun ha 1
  simp at h

/-- The first mixed chart equation has no Jacobian singularity anywhere. -/
theorem family_mixed_chart_nonsingular {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α)
    (x y : ℂ) : ¬ JacobianSingular (familyMixedPolynomial m α (star α)) x y := by
  intro hs
  have hmem := (familyProjectiveCritical_mk_iff m α ![1, x] ![y, 1] (by simp) (by simp)).mpr
    ((family_critical_mixed_iff m α x y).mpr hs)
  rw [family_projective_critical_eq_pair hm ha] at hmem
  rcases hmem with h | h
  · exact projective_mk_one_ne_origin x (Prod.mk.inj h).1
  · exact projective_mk_one_ne_infinity y (Prod.mk.inj (Set.mem_singleton_iff.mp h)).2

/-- G06 for the extremal family, in the four standard chart equations.
The affine origin `(0,0)` and reciprocal origin `(∞,∞)` are ordinary `m`-fold
points. Every other zero of the affine and reciprocal equations, and every zero
of both mixed equations, has multiplicity exactly one. -/
theorem family_ordinary_multiple_points {m : ℕ} (hm : 2 ≤ m) {α : ℂ} (ha : α ≠ star α) :
    OrdinaryAtOrigin (familyPolynomial m α) m ∧
      OrdinaryAtOrigin (familyInfinityPolynomial m α) m ∧
      (∀ x y : ℂ, planeEval x y (familyPolynomial m α) = 0 → ¬ (x = 0 ∧ y = 0) →
        HasMultiplicityAt (familyPolynomial m α) x y 1) ∧
      (∀ u v : ℂ, planeEval u v (familyInfinityPolynomial m α) = 0 → ¬ (u = 0 ∧ v = 0) →
        HasMultiplicityAt (familyInfinityPolynomial m α) u v 1) ∧
      (∀ u y : ℂ, planeEval u y (familyMixedPolynomial m α (star α)) = 0 →
        HasMultiplicityAt (familyMixedPolynomial m α (star α)) u y 1) ∧
      (∀ v x : ℂ, planeEval v x (familyMixedPolynomial m (star α) α) = 0 →
        HasMultiplicityAt (familyMixedPolynomial m (star α) α) v x 1) := by
  have hm0 : 0 < m := by omega
  have ha0 : α ≠ 0 := by intro h; simp [h] at ha
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [family_fourTerm]
    exact fourTermForm_ordinary hm0 ha0 (star_ne_zero.mpr ha0) 1 1
  · exact fourTermForm_ordinary hm0 one_ne_zero one_ne_zero (star α) α
  · intro x y hz hne
    exact hasMultiplicityAt_one hz (fun hs => hne ((family_affine_singular_iff hm ha).mp hs))
  · intro u v hz hne
    exact hasMultiplicityAt_one hz (fun hs => hne ((family_infinity_singular_iff hm ha).mp hs))
  · intro u y hz
    exact hasMultiplicityAt_one hz (family_mixed_chart_nonsingular hm ha u y)
  · intro v x hz
    have hs := family_mixed_chart_nonsingular hm has v x
    rw [star_star] at hs
    exact hasMultiplicityAt_one hz hs

#print axioms mem_pointIdeal_iff
#print axioms jacobianSingular_of_mem_sq
#print axioms binaryForm_eq_prod
#print axioms fourTermForm_ordinary
#print axioms family_mixed_chart_nonsingular
#print axioms family_ordinary_multiple_points

end CurveSymmetry
