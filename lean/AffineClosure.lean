import FamilyRealLocus
import Elimination
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Spectrum.Prime.Topology

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

def affineRealDiagonal (P : BPoly) : Set (Fin 2 → ℂ) :=
  (fun z : ℂ => ![z, star z]) '' realLocus P

lemma mem_realLocus_eval_pair (P : BPoly) (z : ℂ) :
    z ∈ realLocus P ↔ eval ![z, star z] P = 0 := by
  have he : (fun i : Fin 2 => if i = 0 then z else star z) = ![z, star z] := by
    ext i
    fin_cases i <;> simp
  simp only [realLocus, Set.mem_ofPred_eq, he]

/-- An irreducible plane equation with infinitely many real points generates
the entire ideal of polynomials vanishing on those points. -/
theorem real_diagonal_vanishingIdeal {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    vanishingIdeal ℂ (affineRealDiagonal P) = Ideal.span {P} := by
  ext Q
  rw [Ideal.mem_span_singleton]
  constructor
  · intro hQ
    apply dvd_of_realLocus_subset hP hinf
    intro z hz
    apply (mem_realLocus_eval_pair Q z).mpr
    have he := (mem_vanishingIdeal_iff.mp hQ) ![z, star z] ⟨z, hz, rfl⟩
    simpa using he
  · rintro ⟨R, rfl⟩
    apply mem_vanishingIdeal_iff.mpr
    rintro _ ⟨z, hz, rfl⟩
    have he := (mem_realLocus_eval_pair P z).mp hz
    change eval ![z, star z] (P * R) = 0
    rw [map_mul, he, zero_mul]

/-- The complex points cut out by every equation valid on the real locus are
exactly the complex zeroes of the original equation. -/
theorem real_diagonal_algebraic_closure {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    zeroLocus ℂ (vanishingIdeal ℂ (affineRealDiagonal P)) =
      {v : Fin 2 → ℂ | eval v P = 0} := by
  rw [real_diagonal_vanishingIdeal hP hinf, zeroLocus_span]
  ext v
  simp

/-- The ordinary complex-valued point of the prime spectrum obtained by
evaluation, not a custom point or a modified topology. -/
noncomputable def affineSpectrumPoint (v : Fin 2 → ℂ) : PrimeSpectrum BPoly :=
  ⟨RingHom.ker (eval v), RingHom.ker_isPrime (eval v)⟩

theorem spectrum_vanishingIdeal_image (S : Set (Fin 2 → ℂ)) :
    PrimeSpectrum.vanishingIdeal (affineSpectrumPoint '' S) = vanishingIdeal ℂ S := by
  ext P
  rw [PrimeSpectrum.mem_vanishingIdeal, mem_vanishingIdeal_iff]
  constructor
  · intro h v hv
    have he := h (affineSpectrumPoint v) ⟨v, hv, rfl⟩
    change eval v P = 0 at he
    simpa using he
  · intro h q hq
    rcases hq with ⟨v, hv, rfl⟩
    change eval v P = 0
    simpa using h v hv

/-- Genuine Zariski closure in Mathlib's affine prime spectrum. This is the
affine closure statement; projective boundary closure remains separate. -/
theorem real_diagonal_spectrum_closure {P : BPoly} (hP : Irreducible P)
    (hinf : (realLocus P).Infinite) :
    closure (affineSpectrumPoint '' affineRealDiagonal P) =
      PrimeSpectrum.zeroLocus ({P} : Set BPoly) := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    spectrum_vanishingIdeal_image, real_diagonal_vanishingIdeal hP hinf,
    PrimeSpectrum.zeroLocus_span]

theorem family_affine_spectrum_closure {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) :
    closure (affineSpectrumPoint '' affineRealDiagonal (familyPolynomial m α)) =
      PrimeSpectrum.zeroLocus ({familyPolynomial m α} : Set BPoly) :=
  real_diagonal_spectrum_closure (familyPolynomial_irreducible hm ha)
    (family_realLocus_infinite hm ha)

#print axioms real_diagonal_vanishingIdeal
#print axioms real_diagonal_algebraic_closure
#print axioms real_diagonal_spectrum_closure
#print axioms family_affine_spectrum_closure

end CurveSymmetry
