import HolomorphicSpace

/-!
# The differentials `tⁱ·dt/w` (G09b-3c)

For `i < m`, the differential `tⁱ·dt/w` of the family's function field is
holomorphic, and the `m` of them are linearly independent over `ℂ`:

* where `h(c) ≠ 0`, `w` is a unit of the local ring, so `tⁱ/w` lies in it;
* where `h(c) = 0`, `(tⁱ/w)·w = tⁱ` does;
* at infinity, writing `m = i + 1 + j`, the chart sends `tⁱ/w` to
  `s^(j+2)/w'`, and `s·k = w'²` turns `φ(tⁱ/w)/w'³ = s^(j+2)/w'⁴` into
  `w'^(2j)·k^(−(j+2))`, which lies in the local ring because `k` is a unit.

Independence is independence of `1, t, …, t^(m−1)` over `ℂ`, since `dt/w ≠ 0`.
That they span the holomorphic differentials is G09b-3d.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section Point

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

/-- Polynomials in `t` lie in every point place's local ring. -/
lemma quadLocal_poly_mem (p : ℂ[X]) :
    algebraMap ℂ[X] (QuadField h) p ∈ quadLocalRing h c d hd := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]
  exact Subalgebra.algebraMap_mem _ _

/-- The root `w` lies in every point place's local ring. -/
lemma quadLocal_root_mem : AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
  rw [← quadRingMap_root, ← algebraMap_quadRing_apply]
  exact Subalgebra.algebraMap_mem _ _

/-- Where `d ≠ 0`, the root `w` is a unit of the local ring. -/
lemma quadLocal_root_inv_mem (hdne : d ≠ 0) :
    (AdjoinRoot.root (quadRat h))⁻¹ ∈ quadLocalRing h c d hd := by
  have hmem : AdjoinRoot.root (quadPoly h) ∈ (RingHom.ker (quadEval h c d hd)).primeCompl := by
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, RingHom.mem_ker, quadEval_root]
    exact hdne
  have := quadLocal_inv_mem_of_isUnit h c d hd
    (IsLocalization.map_units (quadLocalRing h c d hd) ⟨_, hmem⟩)
  rwa [algebraMap_quadRing_apply, quadRingMap_root] at this

end Point

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

variable (m α) in
/-- The coefficient `tⁱ/w` of the candidate basis differential. -/
noncomputable def holoCoeff (i : ℕ) : QuadField (familyH m α) :=
  quadT (familyH m α) ^ i * (AdjoinRoot.root (quadRat (familyH m α)))⁻¹

variable (m α) in
/-- The differential `tⁱ·dt/w`. -/
noncomputable def holoBasisVec (i : ℕ) : Ω[QuadField (familyH m α)⁄ℂ] :=
  holoCoeff m α i • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))

/-- The chart sends `t` to `1/s` and `w` to `w'·s^(−(m+1))`. -/
lemma familyInfinityMap_holoCoeff (i : ℕ) :
    familyInfinityMap m α (holoCoeff m α i) =
      (quadT (familyH m (star α)))⁻¹ ^ i *
        (AdjoinRoot.root (quadRat (familyH m (star α))) *
          (quadT (familyH m (star α)))⁻¹ ^ (m + 1))⁻¹ := by
  rw [holoCoeff, map_mul, map_pow, map_inv₀, familyInfinityMap_root]
  have ht : familyInfinityMap m α (quadT (familyH m α)) = (quadT (familyH m (star α)))⁻¹ := by
    rw [quadT, familyInfinityMap_t, quadT]
  rw [ht, map_inv₀, ← quadT_eq]

/-- **G09b-3c**: for `i < m`, `tⁱ·dt/w` is holomorphic. -/
theorem holoBasisVec_mem (i : ℕ) (hi : i < m) :
    holoBasisVec m α i ∈ holomorphicDifferentials m α := by
  rw [mem_holomorphicDifferentials, holoBasisVec, isHolomorphic_smul_dt_iff]
  have hw := quadRoot_ne_zero (familyH m α)
  refine ⟨fun c d hd => ⟨fun hc => ?_, fun _ => ?_⟩, ?_⟩
  · -- unramified: `w` is a unit there
    have hdne : d ≠ 0 := by
      intro hzero
      rw [hzero] at hd
      exact hc (by linear_combination -hd)
    rw [holoCoeff]
    refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ i)
      (quadLocal_root_inv_mem _ c d hd hdne)
    rw [quadT]
    exact quadLocal_poly_mem _ c d hd X
  · -- ramified: `(tⁱ/w)·w = tⁱ`
    rw [holoCoeff, mul_assoc, inv_mul_cancel₀ hw, mul_one]
    refine Subalgebra.pow_mem _ ?_ i
    rw [quadT]
    exact quadLocal_poly_mem _ c d hd X
  · -- infinity: `φ(tⁱ/w)/w'³ = w'^(2j)·k^(−(j+2))` with `m = i + 1 + j`
    obtain ⟨j, rfl⟩ : ∃ j, m = i + 1 + j := ⟨m - (i + 1), by omega⟩
    obtain ⟨k₀, hk0, hsk⟩ := familyInfinity_shift_sq (m := i + 1 + j) (α := α)
    have hw' := quadRoot_ne_zero (familyH (i + 1 + j) (star α))
    have hs := quadT_ne_zero (familyH (i + 1 + j) (star α))
    have hk : algebraMap ℂ[X] (QuadField (familyH (i + 1 + j) (star α))) k₀ ≠ 0 := by
      intro hzero
      rw [hzero, mul_zero] at hsk
      exact hw' (pow_eq_zero_iff two_ne_zero |>.mp hsk.symm)
    have hsval : quadT (familyH (i + 1 + j) (star α)) =
        AdjoinRoot.root (quadRat (familyH (i + 1 + j) (star α))) ^ 2 *
          (algebraMap ℂ[X] (QuadField (familyH (i + 1 + j) (star α))) k₀)⁻¹ := by
      rw [← hsk, mul_assoc, mul_inv_cancel₀ hk, mul_one]
    set S := quadT (familyH (i + 1 + j) (star α)) with hSdef
    set W := AdjoinRoot.root (quadRat (familyH (i + 1 + j) (star α))) with hWdef
    set Kk := algebraMap ℂ[X] (QuadField (familyH (i + 1 + j) (star α))) k₀
    have hA : familyInfinityMap (i + 1 + j) α (holoCoeff (i + 1 + j) α i) * (W ^ 3)⁻¹ =
        S ^ (j + 2) * (W ^ 4)⁻¹ := by
      rw [familyInfinityMap_holoCoeff, ← hSdef, ← hWdef]
      field_simp
      rw [one_div, inv_pow, inv_pow, div_eq_mul_inv, inv_inv,
        show i + 1 + j + 1 = i + (j + 2) by ring, pow_add,
        inv_mul_cancel_left₀ (pow_ne_zero i hs)]
    have hval : familyInfinityMap (i + 1 + j) α (holoCoeff (i + 1 + j) α i) * (W ^ 3)⁻¹ =
        W ^ (2 * j) * Kk⁻¹ ^ (j + 2) := by
      rw [hA, hsval]
      generalize Kk⁻¹ = Kinv
      rw [mul_pow, ← pow_mul, show 2 * (j + 2) = 2 * j + 4 by ring, pow_add]
      field_simp
    rw [hval]
    obtain ⟨-, hkinv⟩ := quadLocal_poly_unit (familyH (i + 1 + j) (star α)) 0 0
      (familyH_star_zero_point (i + 1 + j) α) k₀ hk0
    exact Subalgebra.mul_mem _
      (Subalgebra.pow_mem _ (quadLocal_root_mem _ 0 0 _) _)
      (Subalgebra.pow_mem _ hkinv _)

/-- Polynomials in `t` embed injectively into the function field. -/
lemma algebraMap_polynomial_injective :
    Function.Injective (algebraMap ℂ[X] (QuadField (familyH m α))) := by
  rw [IsScalarTower.algebraMap_eq ℂ[X] (RatFunc ℂ) (QuadField (familyH m α))]
  exact (algebraMap (RatFunc ℂ) (QuadField (familyH m α))).injective.comp
    (IsFractionRing.injective ℂ[X] (RatFunc ℂ))

/-- **G09b-3c**: the `m` differentials `tⁱ·dt/w`, `i < m`, are linearly independent over `ℂ`. -/
theorem holoBasisVec_linearIndependent :
    LinearIndependent ℂ (fun i : Fin m => holoBasisVec m α i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hw := quadRoot_ne_zero (familyH m α)
  have hdt := quad_D_t_ne_zero (familyH m α)
  -- collect the coefficients into one polynomial
  set p : ℂ[X] := ∑ i : Fin m, C (g i) * X ^ (i : ℕ) with hp
  have hC : ∀ z : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C z) =
      algebraMap ℂ (QuadField (familyH m α)) z := by
    intro z
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  have hterm : ∀ i : Fin m, g i • holoBasisVec m α i =
      (algebraMap ℂ[X] (QuadField (familyH m α)) (C (g i) * X ^ (i : ℕ)) *
          (AdjoinRoot.root (quadRat (familyH m α)))⁻¹) •
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) := by
    intro i
    rw [holoBasisVec, holoCoeff, ← algebraMap_smul (QuadField (familyH m α)) (g i), smul_smul,
      map_mul, map_pow, hC, quadT, mul_assoc]
  have hsum : ∑ i : Fin m, g i • holoBasisVec m α i =
      (algebraMap ℂ[X] (QuadField (familyH m α)) p *
          (AdjoinRoot.root (quadRat (familyH m α)))⁻¹) •
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) := by
    rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_smul, ← Finset.sum_mul, hp,
      map_sum]
  rw [hsum] at hg
  rcases smul_eq_zero.mp hg with hzero | hzero
  · have hpzero : algebraMap ℂ[X] (QuadField (familyH m α)) p = 0 := by
      rcases mul_eq_zero.mp hzero with h0 | h0
      · exact h0
      · exact absurd (inv_eq_zero.mp h0) hw
    have hp0 : p = 0 := algebraMap_polynomial_injective (by rw [hpzero, map_zero])
    intro i
    have hcoeff := congrArg (fun q : ℂ[X] => q.coeff i) hp0
    simp only [hp, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hcoeff
    rw [Finset.sum_eq_single i (fun b _ hb => by
      rw [ite_eq_right (fun h' => hb (Fin.ext h'.symm)), mul_zero]) (by simp)] at hcoeff
    simpa using hcoeff
  · exact absurd hzero hdt

#print axioms holoBasisVec_mem
#print axioms holoBasisVec_linearIndependent

end CurveSymmetry
