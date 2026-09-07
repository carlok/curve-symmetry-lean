import FamilyBidegree

namespace CurveSymmetry

set_option autoImplicit false
open MvPolynomial

private lemma normalize_homogeneous_pair (a b : ℂ) (hb : b ≠ 0) :
    ![a, b] = b • (![a / b, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- The affine scalar identity extends to all homogeneous coordinates.
Continuity is used only for explicit polynomial functions on complex vector
spaces, not for an unproved topology on projectivization. -/
theorem family_bihomogeneous_transport {m : ℕ} {α β k : ℂ} {g : MobiusMatrix}
    (he : familyMobiusPullback m β g = C k * familyPolynomial m α)
    (x y : Fin 2 → ℂ) :
    familyBihomogeneous m β (g • x) ((g.map (starRingEnd ℂ)) • y) =
      k * familyBihomogeneous m α x y := by
  have haffine (u v : ℂ) :
      familyBihomogeneous m β (g • ![u, 1]) ((g.map (starRingEnd ℂ)) • ![v, 1]) =
        k * familyBihomogeneous m α ![u, 1] ![v, 1] := by
    rw [← familyMobiusPullback_eval, he, map_mul, planeEval_C, familyBihomogeneous_affine]
  let F : ℂ × ℂ → ℂ := fun st =>
    familyBihomogeneous m β (g • ![x 0, st.1]) ((g.map (starRingEnd ℂ)) • ![y 0, st.2])
  let G : ℂ × ℂ → ℂ := fun st => k * familyBihomogeneous m α ![x 0, st.1] ![y 0, st.2]
  have hF : Continuous F := by
    dsimp [F]
    simp only [Matrix.GeneralLinearGroup.fin_two_smul]
    unfold familyBihomogeneous
    fun_prop
  have hG : Continuous G := by
    dsimp [G, familyBihomogeneous]
    fun_prop
  have hdense : Dense (({0}ᶜ : Set ℂ) ×ˢ ({0}ᶜ : Set ℂ)) :=
    (dense_compl_singleton (0 : ℂ)).prod (dense_compl_singleton (0 : ℂ))
  have hFG : F = G := by
    apply Continuous.ext_on hdense hF hG
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    have hs0 : s ≠ 0 := hs
    have ht0 : t ≠ 0 := ht
    dsimp [F, G]
    rw [normalize_homogeneous_pair (x 0) s hs0, normalize_homogeneous_pair (y 0) t ht0,
      smul_comm g s, smul_comm (g.map (starRingEnd ℂ)) t]
    simp only [familyBihomogeneous_smul_left, familyBihomogeneous_smul_right]
    rw [haffine]
    ring
  have hx : ![x 0, x 1] = x := by ext i; fin_cases i <;> rfl
  have hy : ![y 0, y 1] = y := by ext i; fin_cases i <;> rfl
  have h := congrFun hFG (x 1, y 1)
  dsimp [F, G] at h
  simpa only [hx, hy] using h

/-- The nonzero polynomial identity transports the entire product-projective
zero locus, including every boundary chart, in both directions. -/
theorem family_projective_transport_of_identity {m : ℕ} {α β k : ℂ} {g : MobiusMatrix}
    (hk : k ≠ 0) (he : familyMobiusPullback m β g = C k * familyPolynomial m α)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by
  rcases p with ⟨p, q⟩
  induction p using Projectivization.ind with | h x hx =>
  induction q using Projectivization.ind with | h y hy =>
  change (g • Projectivization.mk ℂ x hx,
    (g.map (starRingEnd ℂ)) • Projectivization.mk ℂ y hy) ∈ _ ↔ _
  rw [Projectivization.smul_mk, Projectivization.smul_mk,
    familyProjective_mk_iff, familyProjective_mk_iff, family_bihomogeneous_transport he]
  simp [hk]

/-- Arbitrary inclusion of the spherical real loci forces equivalence of the
constructed complex projective zero loci. This does not yet prove invariance
of the intrinsic singularity condition. -/
theorem family_mobius_complex_transport {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by
  obtain ⟨k, hk, he⟩ := family_mobius_proportional hm ha hb g hmap
  exact family_projective_transport_of_identity hk he p

lemma familyBihomogeneous_swap (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ) :
    familyBihomogeneous m α y x = familyBihomogeneous m (star α) x y := by
  simp only [familyBihomogeneous, star_star]
  ring

lemma familyProjective_swap_iff (m : ℕ) (α : ℂ) (p : ProjectiveLine × ProjectiveLine) :
    p.swap ∈ familyProjectiveCurve m α ↔ p ∈ familyProjectiveCurve m (star α) := by
  change familyBihomogeneous m α p.2.rep p.1.rep = 0 ↔ _
  rw [familyBihomogeneous_swap]
  rfl

lemma sphere_conjugation_involutive (p : Sphere) :
    OnePoint.map (star : ℂ → ℂ) (OnePoint.map (star : ℂ → ℂ) p) = p := by
  cases p using OnePoint.rec <;> simp

lemma conjugate_mem_sphericalFamily_iff {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) (p : Sphere) :
    OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m α ↔ p ∈ sphericalFamily m (star α) := by
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  rw [← sphericalFamily_projective_iff hm ha, sphereRealDiagonal_conjugate,
    familyProjective_swap_iff, sphericalFamily_projective_iff hm has]

/-- The antiholomorphic case also transports the whole projective zero locus;
complex conjugation on the real sphere becomes factor exchange. -/
theorem family_anti_mobius_complex_transport {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β)
    (p : ProjectiveLine × ProjectiveLine) :
    complexifiedAntiMobius g p ∈ familyProjectiveCurve m β ↔ p ∈ familyProjectiveCurve m α := by
  have has : star α ≠ star (star α) := by simpa only [star_star, ne_comm] using ha
  have hhol : ∀ q ∈ sphericalFamily m (star α), g • q ∈ sphericalFamily m β := by
    intro q hq
    have hconj := (conjugate_mem_sphericalFamily_iff hm ha q).mpr hq
    simpa only [sphere_conjugation_involutive] using hmap (OnePoint.map (star : ℂ → ℂ) q) hconj
  change complexifiedMobius g p.swap ∈ familyProjectiveCurve m β ↔ _
  rw [family_mobius_complex_transport hm has hb g hhol, familyProjective_swap_iff, star_star]

/-- For this irreducible family, one-sided Möbius containment is already exact
equivalence of the spherical loci. -/
theorem family_mobius_inclusion_iff {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α, g • p ∈ sphericalFamily m β) (p : Sphere) :
    g • p ∈ sphericalFamily m β ↔ p ∈ sphericalFamily m α := by
  rw [← sphericalFamily_projective_iff hm hb, sphereRealDiagonal_action,
    family_mobius_complex_transport hm ha hb g hmap, sphericalFamily_projective_iff hm ha]

theorem family_anti_mobius_inclusion_iff {m : ℕ} (hm : 0 < m) {α β : ℂ}
    (ha : α ≠ star α) (hb : β ≠ star β) (g : MobiusMatrix)
    (hmap : ∀ p ∈ sphericalFamily m α,
      g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β) (p : Sphere) :
    g • OnePoint.map (star : ℂ → ℂ) p ∈ sphericalFamily m β ↔ p ∈ sphericalFamily m α := by
  rw [← sphericalFamily_projective_iff hm hb, sphereRealDiagonal_anti_action,
    family_anti_mobius_complex_transport hm ha hb g hmap, sphericalFamily_projective_iff hm ha]

#print axioms family_bihomogeneous_transport
#print axioms family_projective_transport_of_identity
#print axioms family_mobius_complex_transport
#print axioms family_anti_mobius_complex_transport
#print axioms family_mobius_inclusion_iff
#print axioms family_anti_mobius_inclusion_iff

end CurveSymmetry
