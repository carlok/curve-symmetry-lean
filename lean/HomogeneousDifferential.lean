import FamilyGlobalTransport
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimension

namespace CurveSymmetry

set_option autoImplicit false

/-- Vanishing of a function and its differential over the base normed field. `HasFDerivAt` is used
instead of the totalized `fderiv`, so nondifferentiability cannot satisfy this
condition accidentally. Its chart-Jacobian interpretation is a separate lemma. -/
def CriticalZero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : E → 𝕜) (x : E) : Prop := F x = 0 ∧ HasFDerivAt F (0 : E →L[𝕜] 𝕜) x

/-- An invertible linear coordinate change and a nonzero constant multiple
preserve the vanishing-differential condition. No regularity is assumed. -/
theorem criticalZero_transport {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (T : E ≃L[𝕜] E) {F G : E → 𝕜} {k : 𝕜} (hk : k ≠ 0)
    (he : ∀ x, G (T x) = k * F x) (x : E) :
    CriticalZero G (T x) ↔ CriticalZero F x := by
  have hfun : G ∘ T = fun y => k * F y := funext he
  have hd : HasFDerivAt (G ∘ T) (0 : E →L[𝕜] 𝕜) x ↔
      HasFDerivAt G (0 : E →L[𝕜] 𝕜) (T x) := by
    simpa using (T.comp_right_hasFDerivAt_iff (f := G) (f' := (0 : E →L[𝕜] 𝕜)))
  constructor
  · rintro ⟨hz, hder⟩
    refine ⟨(mul_eq_zero.mp ((he x).symm.trans hz)).resolve_left hk, ?_⟩
    have h := (hd.mpr hder).const_mul k⁻¹
    rw [hfun] at h
    convert h using 1 <;> first | rfl | (ext v; simp [inv_mul_cancel_left₀ hk])
  · rintro ⟨hz, hder⟩
    refine ⟨by rw [he, hz, mul_zero], hd.mp ?_⟩
    rw [hfun]
    convert hder.const_mul k using 1 <;> first | rfl | (ext v; simp)

abbrev HomogeneousPairs := (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- The actual invertible linear map on the two homogeneous coordinate blocks. -/
noncomputable def homogeneousMobius (g : MobiusMatrix) :
    HomogeneousPairs ≃L[ℂ] HomogeneousPairs :=
  ((DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) g).prodCongr
    (DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) (g.map (starRingEnd ℂ)))).toContinuousLinearEquiv

lemma homogeneousMobius_apply (g : MobiusMatrix) (p : HomogeneousPairs) :
    homogeneousMobius g p = (g • p.1, (g.map (starRingEnd ℂ)) • p.2) := rfl

/-- Transport of the homogeneous critical-zero condition follows from the
proved scalar identity. Projective chart compatibility is not assumed here. -/
theorem family_homogeneous_critical_transport {m : ℕ} {α β k : ℂ} {g : MobiusMatrix}
    (hk : k ≠ 0)
    (he : familyMobiusPullback m β g = MvPolynomial.C k * familyPolynomial m α)
    (p : HomogeneousPairs) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m β q.1 q.2)
      (homogeneousMobius g p) ↔
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) p :=
  criticalZero_transport (homogeneousMobius g) hk
    (fun q => family_bihomogeneous_transport he q.1 q.2) p

/-- Independent nonzero rescaling of either homogeneous block does not change
the condition. This supplies representative independence on `P¹ × P¹`. -/
theorem family_homogeneous_critical_smul (m : ℕ) (α : ℂ) (a b : ℂˣ)
    (p : HomogeneousPairs) :
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
      (a • p.1, b • p.2) ↔
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) p := by
  let T : HomogeneousPairs ≃L[ℂ] HomogeneousPairs :=
    ((DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) a).prodCongr
      (DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) b)).toContinuousLinearEquiv
  apply criticalZero_transport T (k := (a : ℂ) ^ (m + 1) * (b : ℂ) ^ (m + 1))
  · exact mul_ne_zero (pow_ne_zero _ a.ne_zero) (pow_ne_zero _ b.ne_zero)
  · intro q
    change familyBihomogeneous m α (a • q.1) (b • q.2) = _
    simp only [Units.smul_def, familyBihomogeneous_smul_left,
      familyBihomogeneous_smul_right]
    ring

/-- The homogeneous Jacobian condition on the standard product of projective
lines. Representative independence is proved below; equivalence with the
previously computed chart Jacobians remains a separate obligation. -/
def familyProjectiveCritical (m : ℕ) (α : ℂ) : Set (ProjectiveLine × ProjectiveLine) :=
  {p | CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
    (p.1.rep, p.2.rep)}

theorem familyProjectiveCritical_mk_iff (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    (Projectivization.mk ℂ x hx, Projectivization.mk ℂ y hy) ∈
      familyProjectiveCritical m α ↔
    CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2) (x, y) := by
  simp only [familyProjectiveCritical, Set.mem_setOf_eq]
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ x hx
  obtain ⟨b, hb⟩ := Projectivization.exists_smul_eq_mk_rep ℂ y hy
  rw [← ha, ← hb]
  exact family_homogeneous_critical_smul m α a b (x, y)

theorem family_projective_critical_transport_of_identity {m : ℕ} {α β k : ℂ}
    {g : MobiusMatrix} (hk : k ≠ 0)
    (he : familyMobiusPullback m β g = MvPolynomial.C k * familyPolynomial m α)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCritical m β ↔
      p ∈ familyProjectiveCritical m α := by
  rcases p with ⟨p, q⟩
  induction p using Projectivization.ind with | h x hx =>
  induction q using Projectivization.ind with | h y hy =>
  change (g • Projectivization.mk ℂ x hx,
    (g.map (starRingEnd ℂ)) • Projectivization.mk ℂ y hy) ∈ _ ↔ _
  rw [Projectivization.smul_mk, Projectivization.smul_mk,
    familyProjectiveCritical_mk_iff, familyProjectiveCritical_mk_iff]
  exact family_homogeneous_critical_transport hk he (x, y)

/-- This invariance is derived from actual spherical containment. It does not
assume singular-pair preservation or a prescribed form for the Möbius map. -/
theorem family_mobius_projective_critical_transport {m : ℕ} (hm : 0 < m)
    {α β : ℂ} (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCritical m β ↔
      p ∈ familyProjectiveCritical m α := by
  obtain ⟨k, hk, he⟩ := family_mobius_proportional hm ha hb g hmap
  exact family_projective_critical_transport_of_identity hk he p

theorem family_projective_critical_swap (m : ℕ) (α : ℂ)
    (p : ProjectiveLine × ProjectiveLine) :
    p.swap ∈ familyProjectiveCritical m α ↔ p ∈ familyProjectiveCritical m (star α) := by
  let T : HomogeneousPairs ≃L[ℂ] HomogeneousPairs :=
    (LinearEquiv.prodComm ℂ (Fin 2 → ℂ) (Fin 2 → ℂ)).toContinuousLinearEquiv
  have he (q : HomogeneousPairs) :
      familyBihomogeneous m α (T q).1 (T q).2 =
        1 * familyBihomogeneous m (star α) q.1 q.2 := by
    change familyBihomogeneous m α q.2 q.1 = _
    rw [familyBihomogeneous_swap, one_mul]
  convert criticalZero_transport T (k := (1 : ℂ))
    (F := fun q : HomogeneousPairs => familyBihomogeneous m (star α) q.1 q.2)
    (G := fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
    one_ne_zero he (p.1.rep, p.2.rep) using 1 <;> rfl

theorem family_anti_mobius_projective_critical_transport {m : ℕ} (hm : 0 < m)
    {α β : ℂ} (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedAntiMobius g p ∈ familyProjectiveCritical m β ↔
      p ∈ familyProjectiveCritical m α := by
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  have hhol : ∀ q ∈ sphericalFamily m (star α), g • q ∈ sphericalFamily m β := by
    intro q hq
    have hconj := (conjugate_mem_sphericalFamily_iff hm ha q).mpr hq
    simpa only [sphere_conjugation_involutive] using
      hmap (OnePoint.map (star : ℂ → ℂ) q) hconj
  change complexifiedMobius g p.swap ∈ familyProjectiveCritical m β ↔ _
  rw [family_mobius_projective_critical_transport hm has hb g hhol,
    family_projective_critical_swap, star_star]

#print axioms criticalZero_transport
#print axioms family_homogeneous_critical_transport
#print axioms familyProjectiveCritical_mk_iff
#print axioms family_mobius_projective_critical_transport
#print axioms family_anti_mobius_projective_critical_transport

end CurveSymmetry
