import QuadraticInfinity
import Mathlib.Topology.Compactification.OnePoint.Basic

/-!
# Branch points of the double cover (G08)

Recorded choice (user decision, 2026-09-16): a point of the `t`-line is a
*branch point* of the degree-two cover when fewer than two places of the function
field lie over it. A place lies over a finite `c` when `t − c` is a nonunit of it,
and over `∞` when it does not contain `t`. Ramification indices are not defined;
"simple" (index two) is not separately formalized.

`family_branch_points` proves that there are exactly `2m+2` branch points: `∞`
and the `2m+1` distinct roots of `h_α`, which include `0`. Every other point
has exactly two places over it.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial OnePoint

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- In a point place, `1/p(t)` is integral iff `p` does not vanish at the point. -/
lemma quadPlace_poly_inv_mem_iff (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
    (c d : ℂ) (hd : d ^ 2 = h.eval c) (p : ℂ[X]) (hp : p ≠ 0) :
    (algebraMap ℂ[X] (QuadField h) p)⁻¹ ∈ quadPlace h c d hd ↔ p.eval c ≠ 0 := by
  have hA := algebraMap_mem_primeValuationSubring (K := QuadField h)
    (quadEval_ker_ne_bot h c d hd)
  have hcenter := placeCenter_primeValuationSubring (K := QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd)
  have hpeq : algebraMap (QuadRing h) (QuadField h) (AdjoinRoot.of (quadPoly h) p) =
      algebraMap ℂ[X] (QuadField h) p :=
    ((quadRingMap h).commutes p)
  have hmem : AdjoinRoot.of (quadPoly h) p ∈ RingHom.ker (quadEval h c d hd) ↔ p.eval c = 0 := by
    rw [RingHom.mem_ker, quadEval_of]
  have hp0 : algebraMap ℂ[X] (QuadField h) p ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (RatFunc ℂ) (QuadField h)]
    exact (map_ne_zero_iff _ (algebraMap (RatFunc ℂ) (QuadField h)).injective).mpr
      (RatFunc.algebraMap_ne_zero hp)
  change (algebraMap ℂ[X] (QuadField h) p)⁻¹ ∈ primeValuationSubring (QuadField h)
    (RingHom.ker (quadEval h c d hd)) (quadEval_ker_ne_bot h c d hd) ↔ p.eval c ≠ 0
  rw [← hpeq]
  constructor
  · intro hinv hc
    have hin : AdjoinRoot.of (quadPoly h) p ∈ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_notMem_of_mem_placeCenter _ hA hin (hpeq ▸ hp0) hinv
  · intro hc
    have hnot : AdjoinRoot.of (quadPoly h) p ∉ placeCenter (QuadField h)
        (primeValuationSubring (QuadField h) (RingHom.ker (quadEval h c d hd))
          (quadEval_ker_ne_bot h c d hd)) hA := by
      rw [hcenter, hmem]
      exact hc
    exact inv_mem_of_notMem_placeCenter _ hA hnot

variable (m α) in
/-- The places of the function field lying over a point of the `t`-line. -/
def familyPlacesOver (p : OnePoint ℂ) : Set (ValuationSubring (QuadField (familyH m α))) :=
  {O | O ≠ ⊤ ∧ (∀ c : ℂ, algebraMap ℂ[X] (QuadField (familyH m α)) (C c) ∈ O) ∧
    p.elim (algebraMap ℂ[X] (QuadField (familyH m α)) X ∉ O)
      (fun c => algebraMap ℂ[X] (QuadField (familyH m α)) (X - C c) ∈ O ∧
        (algebraMap ℂ[X] (QuadField (familyH m α)) (X - C c))⁻¹ ∉ O)}

variable (m α) in
/-- The recorded definition: fewer than two places over the point. -/
def IsFamilyBranchPoint (p : OnePoint ℂ) : Prop :=
  (familyPlacesOver m α p).ncard < 2

/-- Places over a finite point `c` are exactly the point places `(c, d)`. -/
lemma mem_familyPlacesOver_coe (c : ℂ) (O : ValuationSubring (QuadField (familyH m α))) :
    O ∈ familyPlacesOver m α (c : OnePoint ℂ) ↔
      ∃ (d : ℂ) (hd : d ^ 2 = (familyH m α).eval c), O = quadPlace (familyH m α) c d hd := by
  have hfin := quad_finite_place_classification (familyH m α)
  have hXC : (X - C c : ℂ[X]) ≠ 0 := X_sub_C_ne_zero c
  constructor
  · rintro ⟨htop, hconst, hlie, hinv⟩
    have ht : algebraMap ℂ[X] (QuadField (familyH m α)) X ∈ O := by
      have he : algebraMap ℂ[X] (QuadField (familyH m α)) X =
          algebraMap ℂ[X] (QuadField (familyH m α)) (X - C c) +
            algebraMap ℂ[X] (QuadField (familyH m α)) (C c) := by
        rw [← map_add, sub_add_cancel]
      rw [he]
      exact add_mem hlie (hconst c)
    obtain ⟨c', d, hd, rfl⟩ := place_eq_quadPlace_of_t_mem O htop hconst ht
    have hc : c' = c := by
      by_contra hne
      apply hinv
      rw [quadPlace_poly_inv_mem_iff _ c' d hd _ hXC, eval_sub, eval_X, eval_C, sub_ne_zero]
      exact hne
    subst hc
    exact ⟨d, hd, rfl⟩
  · rintro ⟨d, hd, rfl⟩
    refine ⟨(hfin.1 c d hd).1, fun c' => (hfin.1 c d hd).2 _, (hfin.1 c d hd).2 _, ?_⟩
    rw [quadPlace_poly_inv_mem_iff _ c d hd _ hXC, eval_sub, eval_X, eval_C, sub_self]
    exact fun h => h rfl

/-- The places over `∞` are exactly the place at infinity. -/
lemma familyPlacesOver_infty : familyPlacesOver m α ∞ = {familyInfinityPlace m α} := by
  ext O
  simp only [familyPlacesOver, elim_infty, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨htop, hconst, ht⟩
    exact place_eq_infinity_of_t_notMem O htop hconst ht
  · rintro rfl
    exact ⟨familyInfinityPlace_ne_top, familyInfinityPlace_const, familyInfinityPlace_t_notMem⟩

lemma familyPlacesOver_coe_eq (c : ℂ) :
    familyPlacesOver m α (c : OnePoint ℂ) =
      Set.range (fun d : {d : ℂ // d ^ 2 = (familyH m α).eval c} =>
        quadPlace (familyH m α) c d.1 d.2) := by
  ext O
  rw [mem_familyPlacesOver_coe]
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨d, hd⟩, rfl⟩
  · rintro ⟨⟨d, hd⟩, rfl⟩
    exact ⟨d, hd, rfl⟩

/-- Two places over `c` when `h_α(c) ≠ 0`, one when `h_α(c) = 0`. -/
lemma familyPlacesOver_coe_ncard (c : ℂ) :
    (familyPlacesOver m α (c : OnePoint ℂ)).ncard =
      if (familyH m α).eval c = 0 then 1 else 2 := by
  have hinj : Function.Injective (fun d : {d : ℂ // d ^ 2 = (familyH m α).eval c} =>
      quadPlace (familyH m α) c d.1 d.2) := by
    intro d d' he
    exact Subtype.ext ((quad_finite_place_classification (familyH m α)).2.2 c d.1 c d'.1
      d.2 d'.2 he).2
  rw [familyPlacesOver_coe_eq, Set.ncard_range_of_injective hinj]
  obtain ⟨hne, hzero⟩ := quad_points_over (familyH m α) c
  split_ifs with hc
  · have hset : {d : ℂ | d ^ 2 = (familyH m α).eval c} = {0} := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact hzero hc d
    rw [show Nat.card {d : ℂ // d ^ 2 = (familyH m α).eval c} =
        Nat.card ({d : ℂ | d ^ 2 = (familyH m α).eval c} : Set ℂ) from rfl,
      Nat.card_coe_set_eq, hset, Set.ncard_singleton]
  · obtain ⟨d₀, hd₀, hiff⟩ := hne hc
    have hset : {d : ℂ | d ^ 2 = (familyH m α).eval c} = {d₀, -d₀} := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hiff d
    rw [show Nat.card {d : ℂ // d ^ 2 = (familyH m α).eval c} =
        Nat.card ({d : ℂ | d ^ 2 = (familyH m α).eval c} : Set ℂ) from rfl,
      Nat.card_coe_set_eq, hset, Set.ncard_pair hd₀]

omit hm ha in
/-- `h_α` has exactly `2m+1` distinct roots. -/
lemma familyH_roots_card (hm0 : 0 < m) (hα : α ≠ star α) :
    (familyH m α).roots.toFinset.card = 2 * m + 1 := by
  have hsep : (familyH m α).Separable :=
    PerfectField.separable_iff_squarefree.mpr (familyH_squarefree_of hm0 hα)
  rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
    familyH_natDegree_of hm0 hα]

/-- G08: exactly `2m+2` branch points, namely `∞` and the roots of `h_α` (including
`0`); every point outside them has exactly two places over it. -/
theorem family_branch_points :
    {p : OnePoint ℂ | IsFamilyBranchPoint m α p} =
        insert ∞ (((↑) : ℂ → OnePoint ℂ) '' ((familyH m α).roots.toFinset : Set ℂ)) ∧
      {p : OnePoint ℂ | IsFamilyBranchPoint m α p}.ncard = 2 * m + 2 ∧
      IsFamilyBranchPoint m α ∞ ∧ IsFamilyBranchPoint m α ((0 : ℂ) : OnePoint ℂ) ∧
      ∀ c : ℂ, (familyH m α).eval c ≠ 0 → (familyPlacesOver m α (c : OnePoint ℂ)).ncard = 2 := by
  have hh0 : familyH m α ≠ 0 := (familyH_squarefree_of hm.out ha.out).ne_zero
  have hbranch_coe (c : ℂ) : IsFamilyBranchPoint m α (c : OnePoint ℂ) ↔ (familyH m α).eval c = 0 := by
    unfold IsFamilyBranchPoint
    rw [familyPlacesOver_coe_ncard]
    split_ifs with hc <;> simp [hc]
  have hbranch_infty : IsFamilyBranchPoint m α ∞ := by
    unfold IsFamilyBranchPoint
    rw [familyPlacesOver_infty, Set.ncard_singleton]
    norm_num
  have hset : {p : OnePoint ℂ | IsFamilyBranchPoint m α p} =
      insert ∞ (((↑) : ℂ → OnePoint ℂ) '' ((familyH m α).roots.toFinset : Set ℂ)) := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp [hbranch_infty]
    | coe c =>
        simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image, Finset.mem_coe,
          Multiset.mem_toFinset, mem_roots hh0, IsRoot.def, hbranch_coe]
        constructor
        · intro hc
          exact Or.inr ⟨c, hc, rfl⟩
        · rintro (h | ⟨c', hc', he⟩)
          · exact absurd h (OnePoint.coe_ne_infty c)
          · rw [← OnePoint.coe_injective he]
            exact hc'
  refine ⟨hset, ?_, hbranch_infty, (hbranch_coe 0).mpr (familyH_eval_zero m α), fun c hc => ?_⟩
  · rw [hset, Set.ncard_insert_of_notMem, Set.ncard_image_of_injective _ OnePoint.coe_injective,
      Set.ncard_coe_finset, familyH_roots_card hm.out ha.out]
    · rintro ⟨c, -, hc⟩
      exact OnePoint.coe_ne_infty c hc
  · rw [familyPlacesOver_coe_ncard, ite_eq_right hc]

#print axioms family_branch_points

end CurveSymmetry
