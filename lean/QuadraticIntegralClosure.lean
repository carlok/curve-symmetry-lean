import FamilyFunctionField

/-!
# Integral closure of `ℂ[t]` in a quadratic extension (G07b-1)

For a squarefree `h ∈ ℂ[t]`, an element of `L = ℂ(t)[W]/(W² − h)` is integral
over `ℂ[t]` exactly when it is `a + b·w` with `a, b ∈ ℂ[t]`. Applied to the
family, whose function field G07a identifies with this `L`, it describes the
integral closure of `ℂ[t]`. No places are constructed here.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

/-- `W² − h` over `ℂ(t)`. -/
noncomputable def quadRat (h : ℂ[X]) : (RatFunc ℂ)[X] :=
  X ^ 2 - C (algebraMap ℂ[X] (RatFunc ℂ) h)

/-- The quadratic extension `ℂ(t)[W]/(W² − h)`. -/
abbrev QuadField (h : ℂ[X]) : Type := AdjoinRoot (quadRat h)

/-- A rational function whose square times a squarefree polynomial is polynomial
is itself polynomial. -/
lemma ratFunc_polynomial_of_sq_mul {h : ℂ[X]} (hsq : Squarefree h) {b : RatFunc ℂ} {p : ℂ[X]}
    (hb : b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h = algebraMap ℂ[X] (RatFunc ℂ) p) :
    ∃ c : ℂ[X], b = algebraMap ℂ[X] (RatFunc ℂ) c := by
  have hd0 := RatFunc.denom_ne_zero b
  have hden : algebraMap ℂ[X] (RatFunc ℂ) b.denom ≠ 0 := RatFunc.algebraMap_ne_zero hd0
  have hpoly : b.num ^ 2 * h = p * b.denom ^ 2 := by
    apply RatFunc.algebraMap_injective ℂ
    rw [← RatFunc.num_div_denom b, div_pow] at hb
    field_simp at hb
    simp only [map_pow, map_mul]
    linear_combination hb
  have hdvd : b.denom * b.denom ∣ h := by
    have hc : IsCoprime (b.denom ^ 2) (b.num ^ 2) :=
      (RatFunc.isCoprime_num_denom b).symm.pow
    rw [← sq]
    exact hc.dvd_of_dvd_mul_left ⟨p, by rw [hpoly, mul_comm]⟩
  have hunit : IsUnit b.denom := hsq _ hdvd
  have hone : b.denom = 1 := (RatFunc.monic_denom b).isUnit_iff.mp hunit
  refine ⟨b.num, ?_⟩
  conv_lhs => rw [← RatFunc.num_div_denom b, hone, map_one, div_one]

section

variable (h : ℂ[X])

lemma quadRat_monic : (quadRat h).Monic := monic_X_pow_sub_C _ two_ne_zero

lemma quadRat_natDegree : (quadRat h).natDegree = 2 := natDegree_X_pow_sub_C

instance quadField_nontrivial : Nontrivial (QuadField h) :=
  AdjoinRoot.nontrivial _ (by
    rw [degree_eq_natDegree (quadRat_monic h).ne_zero, quadRat_natDegree]
    decide)

lemma quadRoot_sq :
    AdjoinRoot.root (quadRat h) ^ 2 =
      algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) h) := by
  have h0 : AdjoinRoot.mk (quadRat h) (X ^ 2 - C (algebraMap ℂ[X] (RatFunc ℂ) h)) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
  exact h0

/-- Every element is `a + b·w` with rational-function coefficients. -/
lemma quad_exists_eq (x : QuadField h) :
    ∃ a b : RatFunc ℂ, x = algebraMap (RatFunc ℂ) (QuadField h) a +
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    have hmon := quadRat_monic h
    have hne1 : quadRat h ≠ 1 := by
      intro h1
      have hd := quadRat_natDegree h
      rw [h1, natDegree_one] at hd
      omega
    have hle : (p %ₘ quadRat h).natDegree ≤ 1 := by
      have hlt := natDegree_modByMonic_lt p hmon hne1
      rw [quadRat_natDegree] at hlt
      omega
    have hmk : AdjoinRoot.mk (quadRat h) p = AdjoinRoot.mk (quadRat h) (p %ₘ quadRat h) := by
      rw [AdjoinRoot.mk_eq_mk]
      have hdiv := modByMonic_add_div p (quadRat h)
      exact ⟨p /ₘ quadRat h, by linear_combination -hdiv⟩
    refine ⟨(p %ₘ quadRat h).coeff 0, (p %ₘ quadRat h).coeff 1, ?_⟩
    rw [hmk]
    conv_lhs => rw [eq_X_add_C_of_natDegree_le_one hle]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    rw [← AdjoinRoot.algebraMap_eq]
    ring

lemma eval₂_quadRat {S : Type*} [CommRing S] (i : RatFunc ℂ →+* S) (x : S) :
    (quadRat h).eval₂ i x = x ^ 2 - i (algebraMap ℂ[X] (RatFunc ℂ) h) := by
  simp [quadRat]

/-- The conjugation `w ↦ −w` over `ℂ(t)`. -/
noncomputable def quadConj : QuadField h →ₐ[RatFunc ℂ] QuadField h :=
  AdjoinRoot.liftAlgHom (quadRat h) (Algebra.ofId (RatFunc ℂ) (QuadField h))
    (-AdjoinRoot.root (quadRat h)) (by
    rw [eval₂_quadRat, neg_sq, sub_eq_zero]
    exact quadRoot_sq h)

lemma quadConj_apply (a b : RatFunc ℂ) :
    quadConj h (algebraMap (RatFunc ℂ) (QuadField h) a +
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) =
    algebraMap (RatFunc ℂ) (QuadField h) a -
      algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadConj, AdjoinRoot.liftAlgHom_root]
  ring

/-- Integrality of an element of `ℂ(t)` viewed in `L` descends to `ℂ[t]`. -/
lemma quad_ratFunc_integral {a : RatFunc ℂ}
    (ha : IsIntegral ℂ[X] (algebraMap (RatFunc ℂ) (QuadField h) a)) :
    ∃ p : ℂ[X], algebraMap ℂ[X] (RatFunc ℂ) p = a := by
  have hinj : Function.Injective
      ((Algebra.ofId (RatFunc ℂ) (QuadField h)).restrictScalars ℂ[X]) :=
    (algebraMap (RatFunc ℂ) (QuadField h)).injective
  have ha' := (isIntegral_algHom_iff _ hinj).mp ha
  exact IsIntegrallyClosed.isIntegral_iff.mp ha'

/-- G07b-1 (generic): the integral closure of `ℂ[t]` in `ℂ(t)[W]/(W² − h)` is
`ℂ[t] ⊕ ℂ[t]·w` when `h` is squarefree. -/
theorem quad_isIntegral_iff (hsq : Squarefree h) (x : QuadField h) :
    IsIntegral ℂ[X] x ↔ ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadField h) a +
      algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  have htower (p : ℂ[X]) : algebraMap ℂ[X] (QuadField h) p =
      algebraMap (RatFunc ℂ) (QuadField h) (algebraMap ℂ[X] (RatFunc ℂ) p) :=
    IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h) p
  constructor
  · intro hx
    obtain ⟨a, b, rfl⟩ := quad_exists_eq h x
    have hσ := hx.map ((quadConj h).restrictScalars ℂ[X])
    rw [AlgHom.restrictScalars_apply, quadConj_apply] at hσ
    have htr : IsIntegral ℂ[X] (algebraMap (RatFunc ℂ) (QuadField h) (2 * a)) := by
      have he : algebraMap (RatFunc ℂ) (QuadField h) (2 * a) =
          (algebraMap (RatFunc ℂ) (QuadField h) a +
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) +
          (algebraMap (RatFunc ℂ) (QuadField h) a -
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) := by
        rw [map_mul, map_ofNat]
        ring
      rw [he]
      exact hx.add hσ
    have hnorm : IsIntegral ℂ[X] (algebraMap (RatFunc ℂ) (QuadField h)
        (a ^ 2 - b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h)) := by
      have he : algebraMap (RatFunc ℂ) (QuadField h)
          (a ^ 2 - b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h) =
          (algebraMap (RatFunc ℂ) (QuadField h) a +
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) *
          (algebraMap (RatFunc ℂ) (QuadField h) a -
            algebraMap (RatFunc ℂ) (QuadField h) b * AdjoinRoot.root (quadRat h)) := by
        rw [map_sub, map_mul, map_pow, map_pow]
        linear_combination (algebraMap (RatFunc ℂ) (QuadField h) b) ^ 2 * quadRoot_sq h
      rw [he]
      exact hx.mul hσ
    obtain ⟨p, hp⟩ := quad_ratFunc_integral h htr
    obtain ⟨q, hq⟩ := quad_ratFunc_integral h hnorm
    have ha : a = algebraMap ℂ[X] (RatFunc ℂ) (C (1 / 2 : ℂ) * p) := by
      rw [map_mul, hp, RatFunc.algebraMap_C]
      simp only [map_div₀, map_one, map_ofNat]
      ring
    have hb : b ^ 2 * algebraMap ℂ[X] (RatFunc ℂ) h =
        algebraMap ℂ[X] (RatFunc ℂ) ((C (1 / 2 : ℂ) * p) ^ 2 - q) := by
      rw [map_sub, map_pow, ← ha, hq]
      ring
    obtain ⟨c, hc⟩ := ratFunc_polynomial_of_sq_mul hsq hb
    exact ⟨C (1 / 2 : ℂ) * p, c, by rw [htower, htower, ← ha, ← hc]⟩
  · rintro ⟨a, b, rfl⟩
    have hroot : IsIntegral ℂ[X] (AdjoinRoot.root (quadRat h)) := by
      refine ⟨X ^ 2 - C h, monic_X_pow_sub_C _ two_ne_zero, ?_⟩
      rw [eval₂_sub, eval₂_X_pow, eval₂_C, htower, quadRoot_sq, sub_self]
    exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul hroot)

end

lemma quadRat_familyH (m : ℕ) (α : ℂ) : quadRat (familyH m α) = familyQuadraticRat m α := rfl

/-- G07b-1 for the family: in `ℂ(t)[W]/(W² − h_α)`, which G07a identifies with the
function field of `V_α`, the elements integral over `ℂ[t]` are exactly `a + b·w`
with `a, b ∈ ℂ[t]`. -/
theorem family_isIntegral_iff {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α)
    (x : QuadField (familyH m α)) :
    IsIntegral ℂ[X] x ↔ ∃ a b : ℂ[X], x = algebraMap ℂ[X] (QuadField (familyH m α)) a +
      algebraMap ℂ[X] (QuadField (familyH m α)) b *
        AdjoinRoot.root (quadRat (familyH m α)) :=
  quad_isIntegral_iff (familyH m α) (familyH_squarefree_of hm ha) x

#print axioms ratFunc_polynomial_of_sq_mul
#print axioms quad_isIntegral_iff
#print axioms family_isIntegral_iff

end CurveSymmetry
