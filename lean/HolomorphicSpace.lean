import InfinityRegularity

/-!
# The space of holomorphic differentials of the family (G09b-3b)

A differential of the family's function field is holomorphic when it is regular
at every place. G07b-2c and G07b-3 (`family_place_classification`) show the
places are exactly the point places `(c, d)` with `d² = h_α(c)` and the one place
over `t = ∞`, so holomorphy is regularity at each point place (G09b-1) together
with regularity at infinity (G09b-2, G09b-3a).

Regularity is closed under sums and complex multiples, so the holomorphic
differentials form a `ℂ`-subspace of `Ω[K⁄ℂ]`. Its basis and its dimension, the
genus, are G09b-3c, G09b-3d and G09b-4.
-/

namespace CurveSymmetry

set_option autoImplicit false
open Polynomial

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- Regularity at the place over `t = ∞` is closed under the vector-space operations. -/
lemma isRegularAtInfinity_zero : IsRegularAtInfinity (m := m) (α := α) 0 := by
  rw [IsRegularAtInfinity, map_zero]
  exact isRegularAt_zero _ _ _ _

lemma isRegularAtInfinity_add {ω₁ ω₂ : Ω[QuadField (familyH m α)⁄ℂ]}
    (h₁ : IsRegularAtInfinity ω₁) (h₂ : IsRegularAtInfinity ω₂) :
    IsRegularAtInfinity (ω₁ + ω₂) := by
  rw [IsRegularAtInfinity, map_add]
  exact isRegularAt_add _ _ _ _ h₁ h₂

lemma isRegularAtInfinity_smul (z : ℂ) {ω : Ω[QuadField (familyH m α)⁄ℂ]}
    (h₁ : IsRegularAtInfinity ω) : IsRegularAtInfinity (z • ω) := by
  rw [IsRegularAtInfinity, kaehlerTransport_smul_base]
  exact isRegularAt_smul _ _ _ _ z h₁

/-- A differential of the family's function field is holomorphic when it is regular at every
point place and at the place over `t = ∞`, which by `family_place_classification` are all
the places. -/
def IsHolomorphic (ω : Ω[QuadField (familyH m α)⁄ℂ]) : Prop :=
  (∀ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c),
      IsRegularAt (familyH m α) c d hd ω) ∧
    IsRegularAtInfinity ω

variable (m α) in
/-- **G09b-3b**: the holomorphic differentials, as a complex vector subspace of `Ω[K⁄ℂ]`. -/
def holomorphicDifferentials : Submodule ℂ Ω[QuadField (familyH m α)⁄ℂ] where
  carrier := {ω | IsHolomorphic ω}
  zero_mem' := ⟨fun c d hd => isRegularAt_zero _ c d hd, isRegularAtInfinity_zero⟩
  add_mem' := fun {_ _} ha hb =>
    ⟨fun c d hd => isRegularAt_add _ c d hd (ha.1 c d hd) (hb.1 c d hd),
      isRegularAtInfinity_add ha.2 hb.2⟩
  smul_mem' := fun z {_} ha =>
    ⟨fun c d hd => isRegularAt_smul _ c d hd z (ha.1 c d hd),
      isRegularAtInfinity_smul z ha.2⟩

lemma mem_holomorphicDifferentials (ω : Ω[QuadField (familyH m α)⁄ℂ]) :
    ω ∈ holomorphicDifferentials m α ↔ IsHolomorphic ω :=
  Iff.rfl

/-- Holomorphy of `f·dt`, place by place, with the criteria of G09b-1 and G09b-3a. -/
theorem isHolomorphic_smul_dt_iff (f : QuadField (familyH m α)) :
    IsHolomorphic (f • KaehlerDifferential.D ℂ (QuadField (familyH m α))
        (quadT (familyH m α))) ↔
      (∀ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c),
          ((familyH m α).eval c ≠ 0 → f ∈ quadLocalRing (familyH m α) c d hd) ∧
          ((familyH m α).eval c = 0 →
            f * AdjoinRoot.root (quadRat (familyH m α)) ∈
              quadLocalRing (familyH m α) c d hd)) ∧
        familyInfinityMap m α f *
            (AdjoinRoot.root (quadRat (familyH m (star α))) ^ 3)⁻¹ ∈
          quadLocalRing (familyH m (star α)) 0 0 (familyH_star_zero_point m α) := by
  rw [IsHolomorphic, isRegularAtInfinity_iff_cube]
  refine and_congr ?_ Iff.rfl
  refine forall_congr' fun c => forall_congr' fun d => forall_congr' fun hd => ?_
  by_cases hc : (familyH m α).eval c = 0
  · rw [isRegularAt_ramified _ c d hd hc]
    exact ⟨fun h => ⟨fun h' => absurd hc h', fun _ => h⟩, fun h => h.2 hc⟩
  · rw [isRegularAt_unramified _ c d hd hc]
    exact ⟨fun h => ⟨fun _ => h, fun h' => absurd h' hc⟩, fun h => h.1 hc⟩

#print axioms holomorphicDifferentials
#print axioms isHolomorphic_smul_dt_iff

end CurveSymmetry
