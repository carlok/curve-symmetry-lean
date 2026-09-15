import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Valuation subrings over a Dedekind domain (G07b-2c, generic part)

Let `A` be a Dedekind domain with fraction field `K`. A valuation subring `O` of
`K` containing `A`, other than `K`, has a nonzero prime center `P` in `A`, and
`O` is the localization `A_P` viewed inside `K`. Conversely every nonzero prime
gives such a valuation subring, whose center is that prime. So these valuation
subrings correspond exactly to the nonzero primes of `A`.
-/

namespace CurveSymmetry

set_option autoImplicit false
open IsLocalRing

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K]

variable (K) in
/-- The localization at a prime, as a subalgebra of the fraction field. -/
noncomputable abbrev primeLocalization (P : Ideal A) [P.IsPrime] : Subalgebra A K :=
  Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors

lemma primeLocalization_dvr (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (primeLocalization K P) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _

variable (K) in
/-- The valuation subring `A_P ⊆ K` of a nonzero prime `P`. -/
noncomputable def primeValuationSubring (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    ValuationSubring K where
  toSubring := (primeLocalization K P).toSubring
  mem_or_inv_mem' x := by
    haveI := primeLocalization_dvr (K := K) P hP
    rcases ValuationRing.isInteger_or_isInteger (primeLocalization K P) x with
      ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      rw [← hy]
      exact y.2
    · right
      rw [← hy]
      exact y.2

lemma primeValuationSubring_congr {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hP : P ≠ ⊥)
    (hQ : Q ≠ ⊥) (h : P = Q) : primeValuationSubring K P hP = primeValuationSubring K Q hQ := by
  subst h
  rfl

lemma mem_primeValuationSubring {P : Ideal A} [P.IsPrime] (hP : P ≠ ⊥) (x : K) :
    x ∈ primeValuationSubring K P hP ↔
      ∃ (a s : A) (_ : s ∈ P.primeCompl), x = algebraMap A K a * (algebraMap A K s)⁻¹ :=
  Iff.rfl

lemma algebraMap_mem_primeValuationSubring {P : Ideal A} [P.IsPrime] (hP : P ≠ ⊥) (a : A) :
    algebraMap A K a ∈ primeValuationSubring K P hP :=
  ⟨a, 1, P.primeCompl.one_mem, by simp⟩

variable (K) in
/-- The center in `A` of a valuation subring containing `A`. -/
noncomputable def placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O) :
    Ideal A :=
  Ideal.comap ((algebraMap A K).codRestrict O hO) (maximalIdeal O)

instance placeCenter_isPrime (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O) :
    (placeCenter K O hO).IsPrime := by
  unfold placeCenter
  infer_instance

omit [IsDedekindDomain A] [IsFractionRing A K] in
lemma mem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O) (a : A) :
    a ∈ placeCenter K O hO ↔ O.valuation (algebraMap A K a) < 1 := by
  rw [placeCenter, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

omit [IsDedekindDomain A] [IsFractionRing A K] in
/-- Outside the center, elements of `A` are invertible in `O`. -/
lemma inv_mem_of_notMem_placeCenter (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    {a : A} (ha : a ∉ placeCenter K O hO) : (algebraMap A K a)⁻¹ ∈ O := by
  rw [mem_placeCenter] at ha
  have hle := (O.valuation_le_one_iff _).mpr (hO a)
  have heq : O.valuation (algebraMap A K a) = 1 := le_antisymm hle (not_lt.mp ha)
  rw [← O.valuation_le_one_iff, map_inv₀, heq, inv_one]

lemma placeCenter_ne_bot (O : ValuationSubring K) (hO : ∀ a : A, algebraMap A K a ∈ O)
    (htop : O ≠ ⊤) : placeCenter K O hO ≠ ⊥ := by
  intro hbot
  apply htop
  refine top_unique fun x _ => ?_
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsn : s ∉ placeCenter K O hO := by rw [hbot]; simpa using hs0
  rw [div_eq_mul_inv]
  exact mul_mem (hO a) (inv_mem_of_notMem_placeCenter O hO hsn)

omit [IsDedekindDomain A] in
lemma ofPrime_congr (B : ValuationSubring K) {P Q : Ideal B} [P.IsPrime] [Q.IsPrime]
    (h : P = Q) : B.ofPrime P = B.ofPrime Q := by
  subst h
  rfl

/-- The type `A_P` of the valuation subring is a DVR. -/
lemma primeValuationSubring_dvr (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (primeValuationSubring K P hP) := by
  haveI := primeLocalization_dvr (K := K) P hP
  let e : primeLocalization K P ≃+* primeValuationSubring K P hP :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

/-- A valuation subring other than `K` that contains `A_P` equals `A_P`. -/
theorem eq_primeValuationSubring_of_le (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥)
    (O : ValuationSubring K) (hle : primeValuationSubring K P hP ≤ O) (htop : O ≠ ⊤) :
    O = primeValuationSubring K P hP := by
  let B := primeValuationSubring K P hP
  haveI := primeValuationSubring_dvr (K := K) P hP
  have hof := ValuationSubring.ofPrime_idealOfLE B O hle
  by_cases hb : B.idealOfLE O hle = ⊥
  · exfalso
    apply htop
    rw [← hof, ofPrime_congr B hb, ValuationSubring.ofPrime_bot]
  · have hmax := (inferInstance : (B.idealOfLE O hle).IsPrime).isMaximal_of_ne_bot hb
    rw [← hof, ofPrime_congr B (eq_maximalIdeal hmax), ValuationSubring.ofPrime_top]

/-- The center of `A_P` is `P`. -/
theorem placeCenter_primeValuationSubring (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    placeCenter K (primeValuationSubring K P hP) (algebraMap_mem_primeValuationSubring hP) = P := by
  ext a
  constructor
  · intro ha
    by_contra haP
    have hinv : (algebraMap A K a)⁻¹ ∈ primeValuationSubring K P hP :=
      ⟨1, a, haP, by simp⟩
    rw [mem_placeCenter] at ha
    have h1 := ((primeValuationSubring K P hP).valuation_le_one_iff _).mpr hinv
    rw [map_inv₀] at h1
    have hpos : 0 < (primeValuationSubring K P hP).valuation (algebraMap A K a) := by
      rw [Valuation.pos_iff]
      intro h0
      apply haP
      rw [(IsFractionRing.injective A K) (h0.trans (map_zero _).symm)]
      exact P.zero_mem
    exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr ha)
  · intro haP
    rw [mem_placeCenter]
    by_contra hge
    have hle := ((primeValuationSubring K P hP).valuation_le_one_iff _).mpr
      (algebraMap_mem_primeValuationSubring hP a)
    have heq := le_antisymm hle (not_lt.mp hge)
    have hinv : (algebraMap A K a)⁻¹ ∈ primeValuationSubring K P hP := by
      rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, heq, inv_one]
    obtain ⟨b, s, hs, he⟩ := hinv
    have ha0 : algebraMap A K a ≠ 0 := by
      intro h0
      rw [h0, map_zero] at heq
      exact zero_ne_one heq
    have hs0 : algebraMap A K s ≠ 0 := by
      intro h0
      apply hs
      rw [(IsFractionRing.injective A K) (h0.trans (map_zero _).symm)]
      exact P.zero_mem
    have hab : algebraMap A K s = algebraMap A K (a * b) := by
      rw [map_mul]
      field_simp at he
      linear_combination he
    rw [IsFractionRing.injective A K hab] at hs
    exact hs (P.mul_mem_right b haP)

/-- G07b-2c (generic): a valuation subring of `K` other than `K` containing the
Dedekind domain `A` is the localization at its nonzero center. -/
theorem eq_primeValuationSubring_placeCenter (O : ValuationSubring K)
    (hO : ∀ a : A, algebraMap A K a ∈ O) (htop : O ≠ ⊤) :
    O = primeValuationSubring K (placeCenter K O hO) (placeCenter_ne_bot O hO htop) := by
  apply eq_primeValuationSubring_of_le _ _ O _ htop
  intro x hx
  obtain ⟨a, s, hs, rfl⟩ := hx
  exact mul_mem (hO a) (inv_mem_of_notMem_placeCenter O hO hs)

lemma primeValuationSubring_ne_top (P : Ideal A) [P.IsPrime] (hP : P ≠ ⊥) :
    primeValuationSubring K P hP ≠ ⊤ := by
  intro htop
  obtain ⟨a, haP, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  have hmem : a ∈ placeCenter K (primeValuationSubring K P hP)
      (algebraMap_mem_primeValuationSubring hP) := by
    rw [placeCenter_primeValuationSubring]
    exact haP
  have hinv : (algebraMap A K a)⁻¹ ∈ primeValuationSubring K P hP := by
    rw [htop]
    exact ValuationSubring.mem_top _
  rw [mem_placeCenter] at hmem
  have h1 := ((primeValuationSubring K P hP).valuation_le_one_iff _).mpr hinv
  rw [map_inv₀] at h1
  have hpos : 0 < (primeValuationSubring K P hP).valuation (algebraMap A K a) := by
    rw [Valuation.pos_iff]
    intro h0
    exact ha0 ((IsFractionRing.injective A K) (h0.trans (map_zero _).symm))
  exact absurd ((inv_le_one₀ hpos).mp h1) (not_le.mpr hmem)

/-- Distinct nonzero primes give distinct valuation subrings. -/
lemma primeValuationSubring_injective {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hP : P ≠ ⊥)
    (hQ : Q ≠ ⊥) (he : primeValuationSubring K P hP = primeValuationSubring K Q hQ) : P = Q := by
  have h1 := placeCenter_primeValuationSubring (K := K) P hP
  have h2 := placeCenter_primeValuationSubring (K := K) Q hQ
  rw [← h1, ← h2]
  congr 1

#print axioms eq_primeValuationSubring_placeCenter
#print axioms placeCenter_primeValuationSubring
#print axioms primeValuationSubring_ne_top

end CurveSymmetry
