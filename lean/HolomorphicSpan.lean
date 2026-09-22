import HolomorphicBasis
import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Holomorphic differentials are spanned by `tⁱ·dt/w`; genus `m` (G09b-3d)

* G09b-3d-1: a differential `f·dt` regular at every point place has `f·w` in
  every point place's local ring, hence — `ℂ[t][W]/(W² − h)` being a domain equal
  to the intersection of its localizations at maximal ideals — in that ring:
  `f·w = a(t) + b(t)·w`, that is, `f = a/w + b`.
* G09b-3d-2: at the place over `t = ∞`, read at the conjugate point place
  `(0, 0)` with its valuation `v`, the two parts of `φ(f)/w'³` have valuations
  `v(w')^(2m − 2 − 2·deg a)` and `v(w')^(−2·deg b − 3)`. The exponents differ in
  parity, so the valuation of the sum is the larger one, and the triple zero at
  infinity forces `b = 0` and `deg a ≤ m − 1`.
* G09b-3d-3: the holomorphic differentials are therefore the span of the
  `tⁱ·dt/w`, `i < m`, which G09b-3c showed holomorphic and independent: they
  form a basis, and `family_genus` gives dimension `m`.

`family_genus` reads the genus as the dimension of the holomorphic differentials
of the function field (route B, recorded in the genus scope study). The
identification of that function field with the normalization's is the approved
reading, not a scheme-theoretic theorem. The Riemann–Hurwitz degree identity is
not formalized as a divisor statement.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

section Point

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]

/-- An element of the function field lying in the local ring of every point place comes from
`ℂ[t][W]/(W² − h)`: that ring is the intersection of its localizations at maximal ideals. -/
theorem quad_mem_range_of_forall_local (g : QuadField h)
    (hg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c), g ∈ quadLocalRing h c d hd) :
    ∃ y : QuadRing h, algebraMap (QuadRing h) (QuadField h) y = g := by
  have hbot := MaximalSpectrum.iInf_localization_eq_bot (QuadRing h) (QuadField h)
  have hmem : g ∈ (⊥ : Subalgebra (QuadRing h) (QuadField h)) := by
    rw [← hbot, Algebra.mem_iInf]
    rintro ⟨P, hP⟩
    obtain ⟨c, d, hd, rfl⟩ := (quadRing_isMaximal_iff h P).mp hP
    exact hg c d hd
  rw [Algebra.mem_bot] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, hy⟩

/-- **G09b-3d-1**: if `f·dt` is regular at every point place, then `f·w = a(t) + b(t)·w` for
polynomials `a` and `b`. -/
theorem quad_regular_points_coeff (f : QuadField h)
    (hreg : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      IsRegularAt h c d hd (f • KaehlerDifferential.D ℂ (QuadField h) (quadT h))) :
    ∃ a b : ℂ[X], f * AdjoinRoot.root (quadRat h) =
      algebraMap ℂ[X] (QuadField h) a +
        algebraMap ℂ[X] (QuadField h) b * AdjoinRoot.root (quadRat h) := by
  have hlocal : ∀ (c d : ℂ) (hd : d ^ 2 = h.eval c),
      f * AdjoinRoot.root (quadRat h) ∈ quadLocalRing h c d hd := by
    intro c d hd
    by_cases hc : h.eval c = 0
    · exact (isRegularAt_ramified h c d hd hc f).mp (hreg c d hd)
    · exact Subalgebra.mul_mem _ ((isRegularAt_unramified h c d hd hc f).mp (hreg c d hd))
        (quadLocal_root_mem h c d hd)
  obtain ⟨y, hy⟩ := quad_mem_range_of_forall_local h _ hlocal
  obtain ⟨a, b, rfl⟩ := quadRing_exists_eq h y
  refine ⟨a, b, ?_⟩
  have hroot : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.root (quadPoly h)) =
      AdjoinRoot.root (quadRat h) := by
    rw [algebraMap_quadRing_apply, quadRingMap_root]
  rw [← hy, map_add, map_mul, hroot,
    ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h),
    ← IsScalarTower.algebraMap_apply ℂ[X] (QuadRing h) (QuadField h)]

end Point

#print axioms quad_regular_points_coeff

section Infinity

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- The chart sends a polynomial `p(t)` to `p(1/s)`. -/
lemma familyInfinityMap_poly (p : ℂ[X]) :
    familyInfinityMap m α (algebraMap ℂ[X] (QuadField (familyH m α)) p) =
      aeval (quadT (familyH m (star α)))⁻¹ p := by
  rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField (familyH m α)),
    familyInfinityMap_of, ratInv_algebraMap]
  have hcomm := Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℂ (RatFunc ℂ) (QuadField (familyH m (star α))))
    (RatFunc.X : RatFunc ℂ)⁻¹ p
  rw [IsScalarTower.coe_toAlgHom', map_inv₀, ← quadT_eq] at hcomm
  exact hcomm.symm

/-- Membership in the conjugate local ring is valuation at most one. -/
lemma infinity_mem_iff (x : QuadField (familyH m (star α))) :
    x ∈ quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) ↔
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation x ≤ 1 :=
  ((quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation_le_one_iff x).symm

/-- A unit of the conjugate local ring has valuation one. -/
lemma infinity_val_unit {u : QuadField (familyH m (star α))}
    (hu : u ∈ quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
    (hu' : u⁻¹ ∈ quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α))
    (hne : u ≠ 0) :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation u = 1 := by
  set v := (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
  have h1 : v u ≤ 1 := (infinity_mem_iff u).mp hu
  have h2 : v u⁻¹ ≤ 1 := (infinity_mem_iff _).mp hu'
  rw [map_inv₀] at h2
  have hpos : 0 < v u := (Valuation.pos_iff v).mpr hne
  exact le_antisymm h1 ((inv_le_one₀ hpos).mp h2)

/-- The uniformizer `w'` has valuation strictly between `0` and `1`. -/
lemma infinity_val_root :
    0 < (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
          (AdjoinRoot.root (quadRat (familyH m (star α)))) ∧
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
          (AdjoinRoot.root (quadRat (familyH m (star α)))) < 1 := by
  set v := (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
  set O := quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
  set w := AdjoinRoot.root (quadRat (familyH m (star α)))
  have hw : w ≠ 0 := quadRoot_ne_zero _
  have hwmem : w ∈ O := quadLocal_root_mem _ 0 0 _
  refine ⟨(Valuation.pos_iff v).mpr hw, lt_of_le_of_ne ((infinity_mem_iff w).mp hwmem) ?_⟩
  intro hone
  -- then `w⁻¹` would lie in the local ring, making the uniformizer a unit
  have hinv : w⁻¹ ∈ O := by
    rw [infinity_mem_iff, map_inv₀, hone, inv_one]
  have hunit : IsUnit (⟨w, hwmem⟩ : O) :=
    (Units.mk (⟨w, hwmem⟩ : O) ⟨w⁻¹, hinv⟩ (Subtype.ext (mul_inv_cancel₀ hw))
      (Subtype.ext (inv_mul_cancel₀ hw))).isUnit
  have hmax : (⟨w, hwmem⟩ : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [quad_ramified_uniformizer _ 0 0 (familyH_star_zero_point m α)
      (familyH_eval_zero m (star α))]
    have heq : (⟨w, hwmem⟩ : O) = algebraMap (QuadRing (familyH m (star α))) O
        (AdjoinRoot.root (quadPoly (familyH m (star α)))) :=
      Subtype.ext (quad_ramified_uniformizer_coe _ 0 0 _).symm
    rw [heq]
    exact Ideal.mem_span_singleton_self _
  exact (IsLocalRing.mem_maximalIdeal _).mp hmax hunit

/-- `v(s) = v(w')²`, from `s·k = w'²` with `k` a unit. -/
lemma infinity_val_s :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (quadT (familyH m (star α))) =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (AdjoinRoot.root (quadRat (familyH m (star α)))) ^ 2 := by
  obtain ⟨k₀, hk0, hsk⟩ := familyInfinity_shift_sq (m := m) (α := α)
  obtain ⟨hkmem, hkinv⟩ := quadLocal_poly_unit _ 0 0 (familyH_star_zero_point m α) k₀ hk0
  have hk : algebraMap ℂ[X] (QuadField (familyH m (star α))) k₀ ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hsk
    exact quadRoot_ne_zero _ (pow_eq_zero_iff two_ne_zero |>.mp hsk.symm)
  have hvk := infinity_val_unit hkmem hkinv hk
  have hv := congrArg (quadPlace (familyH m (star α)) 0 0
    (familyH_star_zero_point m α)).valuation hsk
  rw [map_mul, hvk, mul_one, map_pow] at hv
  exact hv

/-- For `p ≠ 0`, `v(p(1/s)) = v(w')^(−2·deg p)`: `s^(deg p)·p(1/s)` is the reversed polynomial
evaluated at `s`, a unit because its constant term is the leading coefficient of `p`. -/
lemma infinity_val_poly (p : ℂ[X]) (hp : p ≠ 0) :
    (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (aeval (quadT (familyH m (star α)))⁻¹ p) =
      (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation
        (AdjoinRoot.root (quadRat (familyH m (star α)))) ^ (-(2 * (p.natDegree : ℤ))) := by
  have hs := quadT_ne_zero (familyH m (star α))
  let : Invertible (quadT (familyH m (star α)))⁻¹ := invertibleOfNonzero (inv_ne_zero hs)
  have hrev := Polynomial.eval₂_reverse_mul_pow
    (algebraMap ℂ (QuadField (familyH m (star α)))) (quadT (familyH m (star α)))⁻¹ p
  rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def] at hrev
  have hsq : aeval (quadT (familyH m (star α))) (reverse p) =
      algebraMap ℂ[X] (QuadField (familyH m (star α))) (reverse p) := by
    rw [quadT, aeval_algebraMap_apply, aeval_X_left_apply]
  have hrev0 : (reverse p).eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
    exact leadingCoeff_ne_zero.mpr hp
  obtain ⟨hrmem, hrinv⟩ := quadLocal_poly_unit _ 0 0 (familyH_star_zero_point m α)
    (reverse p) hrev0
  have hrne : algebraMap ℂ[X] (QuadField (familyH m (star α))) (reverse p) ≠ 0 := by
    intro hzero
    have := algebraMap_polynomial_injective (m := m) (α := star α)
      (hzero.trans (map_zero _).symm)
    exact hp (reverse_eq_zero.mp this)
  have hvr := infinity_val_unit hrmem hrinv hrne
  rw [← hrev, hsq, map_mul, hvr, one_mul, map_pow, map_inv₀, infinity_val_s, zpow_neg,
    show (2 * (p.natDegree : ℤ)) = ((2 * p.natDegree : ℕ) : ℤ) by push_cast; ring,
    zpow_natCast, pow_mul, inv_pow]

/-- Exponent bookkeeping for the `a/w` part at infinity. -/
lemma zpow_combine_even {G : Type*} [CommGroupWithZero G] {γ : G} (hγ : γ ≠ 0) (n m : ℕ) :
    γ ^ (-(2 * (n : ℤ))) * (γ * (γ ^ 2)⁻¹ ^ (m + 1))⁻¹ * (γ ^ 3)⁻¹ =
      γ ^ (2 * (m : ℤ) - 2 - 2 * n) := by
  lift γ to Gˣ using (Ne.isUnit hγ)
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
    ← Units.val_zpow_eq_zpow_val]
  congr 1
  group

/-- Exponent bookkeeping for the `b` part at infinity. -/
lemma zpow_combine_odd {G : Type*} [CommGroupWithZero G] {γ : G} (hγ : γ ≠ 0) (n : ℕ) :
    γ ^ (-(2 * (n : ℤ))) * (γ ^ 3)⁻¹ = γ ^ (-(2 * (n : ℤ)) - 3) := by
  lift γ to Gˣ using (Ne.isUnit hγ)
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_inv_eq_inv_val, ← Units.val_mul,
    ← Units.val_zpow_eq_zpow_val]
  congr 1
  group

#print axioms infinity_val_root

/-- **G09b-3d-2**: a holomorphic `f·dt` has `f = a(t)/w` with `deg a < m`. By G09b-3d-1,
`f = a/w + b`. Read at the conjugate place `(0, 0)` through the chart, `φ(f)/w'³` splits into
a term of valuation `v(w')^(2m − 2 − 2·deg a)` and one of valuation `v(w')^(−2·deg b − 3)`.
The exponents have different parity, so the valuation of the sum is the larger of the two, and
the triple zero at infinity forces `b = 0` and `deg a ≤ m − 1`. -/
theorem holomorphic_coeff_form (f : QuadField (familyH m α))
    (hf : IsHolomorphic (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
      (quadT (familyH m α)))) :
    ∃ a : ℂ[X], a.natDegree < m ∧
      f = algebraMap ℂ[X] (QuadField (familyH m α)) a *
        (AdjoinRoot.root (quadRat (familyH m α)))⁻¹ := by
  obtain ⟨a, b, hab⟩ := quad_regular_points_coeff (familyH m α) f hf.1
  have hinf := (isRegularAtInfinity_iff_cube f).mp hf.2
  have hw : AdjoinRoot.root (quadRat (familyH m α)) ≠ 0 := quadRoot_ne_zero _
  have hfab : f = algebraMap ℂ[X] (QuadField (familyH m α)) a *
      (AdjoinRoot.root (quadRat (familyH m α)))⁻¹ + algebraMap ℂ[X] (QuadField (familyH m α)) b := by
    have : f = (f * AdjoinRoot.root (quadRat (familyH m α))) *
        (AdjoinRoot.root (quadRat (familyH m α)))⁻¹ := by
      rw [mul_assoc, mul_inv_cancel₀ hw, mul_one]
    rw [this, hab, add_mul, mul_assoc (algebraMap ℂ[X] _ b), mul_inv_cancel₀ hw, mul_one]
  set v := (quadPlace (familyH m (star α)) 0 0 (familyH_star_zero_point m α)).valuation with hv
  set W := AdjoinRoot.root (quadRat (familyH m (star α))) with hW
  set S := quadT (familyH m (star α)) with hS
  obtain ⟨hγpos, hγlt⟩ := infinity_val_root (m := m) (α := α)
  have hγ0 : v W ≠ 0 := ne_of_gt hγpos
  have hφw : familyInfinityMap m α (AdjoinRoot.root (quadRat (familyH m α))) =
      W * S⁻¹ ^ (m + 1) := by
    rw [familyInfinityMap_root, map_inv₀, ← quadT_eq]
  set A := aeval S⁻¹ a * (W * S⁻¹ ^ (m + 1))⁻¹ * (W ^ 3)⁻¹ with hA
  set B := aeval S⁻¹ b * (W ^ 3)⁻¹ with hB
  have hX : familyInfinityMap m α f * (W ^ 3)⁻¹ = A + B := by
    rw [hfab, map_add, map_mul, map_inv₀, familyInfinityMap_poly, familyInfinityMap_poly, hφw,
      hA, hB]
    ring
  rw [hX] at hinf
  have hvle : v (A + B) ≤ 1 := (infinity_mem_iff _).mp hinf
  have hvS : v S⁻¹ = (v W ^ 2)⁻¹ := by rw [map_inv₀, infinity_val_s]
  have hvA : a ≠ 0 → v A = v W ^ (2 * (m : ℤ) - 2 - 2 * a.natDegree) := by
    intro ha0
    rw [hA, map_mul, map_mul, map_inv₀, map_inv₀, map_mul, map_pow, map_pow, hvS,
      infinity_val_poly a ha0]
    exact zpow_combine_even hγ0 a.natDegree m
  have hvB : b ≠ 0 → v B = v W ^ (-(2 * (b.natDegree : ℤ)) - 3) := by
    intro hb0
    rw [hB, map_mul, map_inv₀, map_pow, infinity_val_poly b hb0]
    exact zpow_combine_odd hγ0 b.natDegree
  have hanti := zpow_right_strictAnti₀ hγpos hγlt
  -- the `b` part cannot survive
  have hb : b = 0 := by
    by_contra hb0
    have hBle : v B ≤ 1 := by
      by_cases ha0 : a = 0
      · have hA0 : A = 0 := by rw [hA, ha0, map_zero, zero_mul, zero_mul]
        rwa [hA0, zero_add] at hvle
      · have hne : v A ≠ v B := by
          rw [hvA ha0, hvB hb0]
          intro heq
          have := hanti.injective heq
          omega
        rw [Valuation.map_add_of_distinct_val v hne] at hvle
        exact le_trans (le_max_right _ _) hvle
    rw [hvB hb0, zpow_le_one_iff_right_of_lt_one₀ hγpos hγlt] at hBle
    omega
  refine ⟨a, ?_, by rw [hfab, hb, map_zero, add_zero]⟩
  by_cases ha0 : a = 0
  · rw [ha0, natDegree_zero]
    exact hm.out
  · have hB0 : B = 0 := by rw [hB, hb, map_zero, zero_mul]
    rw [hB0, add_zero, hvA ha0, zpow_le_one_iff_right_of_lt_one₀ hγpos hγlt] at hvle
    omega

#print axioms holomorphic_coeff_form

/-- A polynomial of degree less than `m`, divided by `w`, gives the corresponding combination
of the `tⁱ·dt/w`. -/
lemma poly_div_root_smul_dt (a : ℂ[X]) (ha : a.natDegree < m) :
    (algebraMap ℂ[X] (QuadField (familyH m α)) a * (AdjoinRoot.root (quadRat (familyH m α)))⁻¹) •
        KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α)) =
      ∑ i : Fin m, a.coeff i • holoBasisVec m α i := by
  have hsum : a = ∑ i : Fin m, C (a.coeff i) * X ^ (i : ℕ) := by
    conv_lhs => rw [a.as_sum_range' m ha]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (monomial i) (a.coeff i))]
    simp only [C_mul_X_pow_eq_monomial]
  have hC : ∀ z : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C z) =
      algebraMap ℂ (QuadField (familyH m α)) z := by
    intro z
    rw [Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  conv_lhs => rw [hsum]
  rw [map_sum, Finset.sum_mul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [holoBasisVec, holoCoeff, ← algebraMap_smul (QuadField (familyH m α)) (a.coeff i), smul_smul,
    map_mul, map_pow, hC, quadT, mul_assoc]

/-- **G09b-3d-3**: the holomorphic differentials are exactly the span of the `tⁱ·dt/w`,
`i < m`. -/
theorem holomorphicDifferentials_eq_span :
    holomorphicDifferentials m α =
      Submodule.span ℂ (Set.range fun i : Fin m => holoBasisVec m α i) := by
  refine le_antisymm ?_ ?_
  · intro ω hω
    obtain ⟨f, rfl⟩ := quad_exists_smul_D_t (familyH m α) ω
    obtain ⟨a, hadeg, rfl⟩ := holomorphic_coeff_form f hω
    rw [poly_div_root_smul_dt a hadeg]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact holoBasisVec_mem i i.2

/-- **G09b-3d**: the `tⁱ·dt/w`, `i < m`, form a basis of the holomorphic differentials. -/
noncomputable def holomorphicBasis :
    Module.Basis (Fin m) ℂ (holomorphicDifferentials m α) :=
  (Module.Basis.span (holoBasisVec_linearIndependent (m := m) (α := α))).map
    (LinearEquiv.ofEq _ _ holomorphicDifferentials_eq_span.symm)

/-- **Genus of the family**: with genus read as the dimension of the space of holomorphic
differentials of the function field (the recorded route B), the curve `V_α` has genus `m`. -/
theorem family_genus : Module.finrank ℂ (holomorphicDifferentials m α) = m := by
  rw [Module.finrank_eq_card_basis (holomorphicBasis (m := m) (α := α)), Fintype.card_fin]

#print axioms holomorphicDifferentials_eq_span
#print axioms family_genus

end Infinity

end CurveSymmetry
