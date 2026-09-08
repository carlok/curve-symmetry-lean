import AffineClosure
import FamilyCharts
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

private theorem irreducible_factor_in_prime (p : PrimeSpectrum BPoly) (F : BPoly) :
    F ≠ 0 → F ∈ p.asIdeal →
      ∃ q : BPoly, Irreducible q ∧ q ∣ F ∧ q ∈ p.asIdeal := by
  induction F using WfDvdMonoid.induction_on_irreducible with
  | zero => intro h; exact (h rfl).elim
  | unit u hu =>
      intro _ hmem
      exact (p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)).elim
  | mul a i ha hi ih =>
      intro _ hmem
      rcases p.isPrime.mem_or_mem hmem with hiI | haI
      · exact ⟨i, hi, dvd_mul_right i a, hiI⟩
      · obtain ⟨q, hq, hqa, hqI⟩ := ih ha haI
        exact ⟨q, hq, dvd_mul_of_dvd_right hqa i, hqI⟩

/-- Deleting an irreducible coordinate divisor not dividing the equation
does not change the hypersurface's Zariski closure. This argument also allows
reducible equations: each component's generic point avoids the deleted axis. -/
theorem hypersurface_deleted_axis_closure (F u : BPoly) (hu : Irreducible u)
    (hnot : ¬ u ∣ F) :
    closure (PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
      {p : PrimeSpectrum BPoly | u ∉ p.asIdeal}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by
  apply Set.Subset.antisymm
  · exact closure_minimal Set.inter_subset_left (PrimeSpectrum.isClosed_zeroLocus _)
  · intro p hp
    have hF0 : F ≠ 0 := by intro h; apply hnot; simp [h]
    have hpF : F ∈ p.asIdeal := hp (Set.mem_singleton F)
    obtain ⟨q, hq, hqF, hqp⟩ := irreducible_factor_in_prime p F hF0 hpF
    let η : PrimeSpectrum BPoly := ⟨Ideal.span {q}, Ideal.isPrime_span_singleton_of_prime hq.prime⟩
    have hη : η ∈ PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
        {p : PrimeSpectrum BPoly | u ∉ p.asIdeal} := by
      constructor
      · intro f hf
        rcases Set.mem_singleton_iff.mp hf with rfl
        exact Ideal.mem_span_singleton.mpr hqF
      · intro hqu
        have hd : q ∣ u := Ideal.mem_span_singleton.mp hqu
        exact hnot ((hq.associated_of_dvd hu hd).symm.dvd.trans hqF)
    have hpη : p ∈ closure ({η} : Set (PrimeSpectrum BPoly)) := by
      rw [PrimeSpectrum.closure_singleton]
      change Ideal.span {q} ≤ p.asIdeal
      exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hqp)
    exact closure_mono (Set.singleton_subset_iff.mpr hη) hpη

lemma coordinate_zero_irreducible : Irreducible (X 0 : BPoly) := by
  have h := (Polynomial.irreducible_X (R := UPoly)).map toNested.symm.toMulEquiv
  have he : toNested.symm Polynomial.X = (X 0 : BPoly) := by
    apply toNested.injective
    rw [AlgEquiv.apply_symm_apply, toNested_X_zero]
  change Irreducible (toNested.symm Polynomial.X) at h
  rwa [he] at h

lemma mixed_not_dvd_coordinate {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    ¬ (X 0 : BPoly) ∣ familyMixedPolynomial m a b := by
  rintro ⟨Q, he⟩
  have h := congrArg (planeEval 0 1) he
  simp [familyMixedPolynomial, hm.ne'] at h

/-- In the mixed chart `u=1/X`, the locus with `u ≠ 0` is Zariski dense in
the whole chart curve, including its origin representing `(∞,0)`. -/
theorem mixed_chart_punctured_closure {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    closure (PrimeSpectrum.zeroLocus ({familyMixedPolynomial m a b} : Set BPoly) ∩
      {p : PrimeSpectrum BPoly | (X 0 : BPoly) ∉ p.asIdeal}) =
      PrimeSpectrum.zeroLocus ({familyMixedPolynomial m a b} : Set BPoly) :=
  hypersurface_deleted_axis_closure _ _ coordinate_zero_irreducible (mixed_not_dvd_coordinate hm a b)

theorem mixed_corner_mem_chart_closure {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (PrimeSpectrum.zeroLocus ({familyMixedPolynomial m a b} : Set BPoly) ∩
        {p : PrimeSpectrum BPoly | (X 0 : BPoly) ∉ p.asIdeal}) := by
  rw [mixed_chart_punctured_closure hm]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyMixedPolynomial m a b) = 0
  simp [familyMixedPolynomial, hm.ne']

private lemma affineSpectrumPoint_asIdeal (v : Fin 2 → ℂ) :
    (affineSpectrumPoint v).asIdeal = vanishingIdeal ℂ {v} := by
  ext P
  rw [mem_vanishingIdeal_singleton_iff]
  rfl

lemma closedPoint_iff_affineSpectrumPoint (p : PrimeSpectrum BPoly) :
    p ∈ closedPoints (PrimeSpectrum BPoly) ↔ ∃ v, affineSpectrumPoint v = p := by
  rw [mem_closedPoints_iff, PrimeSpectrum.isClosed_singleton_iff_isMaximal]
  constructor
  · intro h
    obtain ⟨v, hv⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ h
    refine ⟨v, PrimeSpectrum.ext ?_⟩
    rw [affineSpectrumPoint_asIdeal, hv]
  · rintro ⟨v, rfl⟩
    rw [affineSpectrumPoint_asIdeal]
    infer_instance

lemma punctured_complex_points_image (F u : BPoly) :
    affineSpectrumPoint '' {v : Fin 2 → ℂ | eval v F = 0 ∧ eval v u ≠ 0} =
      (PrimeSpectrum.zeroLocus ({F} : Set BPoly) ∩
        {p : PrimeSpectrum BPoly | u ∉ p.asIdeal}) ∩ closedPoints (PrimeSpectrum BPoly) := by
  ext p
  constructor
  · rintro ⟨v, ⟨hF, hu⟩, rfl⟩
    refine ⟨⟨?_, hu⟩, (closedPoint_iff_affineSpectrumPoint _).mpr ⟨v, rfl⟩⟩
    intro q hq
    rcases Set.mem_singleton_iff.mp hq with rfl
    exact hF
  · rintro ⟨⟨hF, hu⟩, hc⟩
    obtain ⟨v, rfl⟩ := (closedPoint_iff_affineSpectrumPoint p).mp hc
    exact ⟨v, ⟨hF (Set.mem_singleton F), hu⟩, rfl⟩

/-- The punctured hypersurface is already dense using ordinary complex
evaluation points; generic spectral points are not being substituted for them. -/
theorem punctured_complex_points_closure (F u : BPoly) (hu : Irreducible u)
    (hnot : ¬ u ∣ F) :
    closure (affineSpectrumPoint '' {v : Fin 2 → ℂ | eval v F = 0 ∧ eval v u ≠ 0}) =
      PrimeSpectrum.zeroLocus ({F} : Set BPoly) := by
  rw [punctured_complex_points_image,
    JacobsonSpace.closure_inter_closedPoints_eq_closure,
    hypersurface_deleted_axis_closure F u hu hnot]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isLocallyClosed.inter
    (PrimeSpectrum.basicOpen u).isOpen.isLocallyClosed

/-- The mixed corner is in the Zariski closure of actual complex chart points
with nonzero `u`. Their original coordinate `X=1/u` is therefore finite. -/
theorem mixed_corner_mem_complex_closure {m : ℕ} (hm : 0 < m) (a b : ℂ) :
    affineSpectrumPoint ![0, 0] ∈
      closure (affineSpectrumPoint '' {v : Fin 2 → ℂ |
        eval v (familyMixedPolynomial m a b) = 0 ∧ v 0 ≠ 0}) := by
  have he : {v : Fin 2 → ℂ | eval v (familyMixedPolynomial m a b) = 0 ∧ v 0 ≠ 0} =
      {v : Fin 2 → ℂ | eval v (familyMixedPolynomial m a b) = 0 ∧ eval v (X 0) ≠ 0} := by simp
  rw [he, punctured_complex_points_closure _ _ coordinate_zero_irreducible
    (mixed_not_dvd_coordinate hm a b)]
  intro f hf
  rcases Set.mem_singleton_iff.mp hf with rfl
  change eval ![0, 0] (familyMixedPolynomial m a b) = 0
  simp [familyMixedPolynomial, hm.ne']

#print axioms hypersurface_deleted_axis_closure
#print axioms mixed_chart_punctured_closure
#print axioms mixed_corner_mem_chart_closure
#print axioms punctured_complex_points_closure
#print axioms mixed_corner_mem_complex_closure

end CurveSymmetry
