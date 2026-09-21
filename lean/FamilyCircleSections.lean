import FamilyEuclidean
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace CurveSymmetry
set_option autoImplicit false
noncomputable section

/-- Two points of the family on the same nonzero centered circle differ by
one of the 2m root rotations. No normalization of alpha is needed. -/
theorem family_equal_norm_ratio_root {m : ℕ} {α z w : ℂ}
    (ha : α ≠ star α) (hz : z ∈ extremalCurve m α) (hw : w ∈ extremalCurve m α)
    (hn : ‖z‖ = ‖w‖) (hw0 : w ≠ 0) : (z / w) ^ (2 * m) = 1 := by
  let b : ℂ := (‖w‖ : ℂ) ^ 2 + α
  have hb : b ≠ 0 := by
    intro h
    have hs := congrArg star h
    simp only [b, star_add, star_pow, star_real_cast, star_zero] at hs
    apply ha
    dsimp [b] at h
    linear_combination h - hs
  have hzre : (z ^ m * b).re = 0 := by
    change (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0 at hz
    simpa [b, hn] using hz
  have hwre : (w ^ m * b).re = 0 := hw
  have he : (z / w) ^ m = (z ^ m * b) / (w ^ m * b) := by
    rw [div_pow]
    field_simp
  have him : ((z / w) ^ m).im = 0 := by
    rw [he, Complex.div_im, hzre, hwre]
    simp
  have hnorm : ‖(z / w) ^ m‖ = 1 := by
    simp [norm_pow, hn, norm_ne_zero_iff.mpr hw0]
  have hs : star ((z / w) ^ m) = (z / w) ^ m := Complex.conj_eq_iff_im.mpr him
  have hmul := mul_star_eq_one_of_norm hnorm
  rw [hs] at hmul
  calc
    (z / w) ^ (2 * m) = (z / w) ^ m * (z / w) ^ m := by rw [← pow_add]; congr 1; omega
    _ = 1 := hmul

/-- The circle section is a single free orbit of the root rotations. -/
def familyCircleRootEquiv {m : ℕ} [NeZero (2 * m)] (hm : 0 < m) {α w : ℂ}
    (ha : α ≠ star α) (hw : w ∈ extremalCurve m α) (hw0 : w ≠ 0) :
    rootsOfUnity (2 * m) ℂ ≃ {z : ℂ // z ∈ extremalCurve m α ∧ ‖z‖ = ‖w‖} :=
  Equiv.ofBijective
    (fun u =>
      have hs := family_root_symmetry hm ((mem_rootsOfUnity' _ _).mp u.property) α
      ⟨(u.val : ℂ) * w, by
        constructor
        · rw [← family_locus_eq] at hw ⊢
          simpa only [add_zero] using (hs.2 w).mpr hw
        · rw [norm_mul, hs.1, one_mul]⟩)
    ⟨by
        intro u v h
        apply rootsOfUnity.coe_injective
        exact mul_right_cancel₀ hw0 (congrArg Subtype.val h),
      by
        intro z
        have hr := family_equal_norm_ratio_root ha z.property.1 hw z.property.2 hw0
        refine ⟨rootsOfUnity.mkOfPowEq (z.val / w) hr, ?_⟩
        apply Subtype.ext
        exact div_mul_cancel₀ z.val hw0⟩

/-- Every positive-radius centered circle meets the family in exactly 2m points. -/
theorem family_circle_section_card {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) {r : ℝ} (hr : 0 < r) :
    Nat.card {z : ℂ // z ∈ extremalCurve m α ∧ ‖z‖ = r} = 2 * m := by
  let : NeZero (2 * m) := ⟨by omega⟩
  obtain ⟨w, hw, hwr⟩ := family_point_of_norm hm ha hr.le
  rw [family_locus_eq] at hw
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwr; linarith
  rw [← hwr, ← Nat.card_congr (familyCircleRootEquiv hm ha hw hw0),
    Complex.card_rootsOfUnity]

/-- The same count stated with the ordinary metric circle. -/
theorem family_metric_circle_card {m : ℕ} (hm : 0 < m) {α : ℂ}
    (ha : α ≠ star α) {r : ℝ} (hr : 0 < r) :
    Nat.card ↥(extremalCurve m α ∩ Metric.sphere (0 : ℂ) r) = 2 * m := by
  change Nat.card {z : ℂ // z ∈ extremalCurve m α ∧ dist z 0 = r} = _
  simpa only [dist_zero_right] using
    family_circle_section_card hm ha hr

#print axioms family_circle_section_card
#print axioms family_metric_circle_card
end
end CurveSymmetry
