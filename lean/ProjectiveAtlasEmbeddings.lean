import ProjectiveAffineEmbedding

namespace CurveSymmetry

set_option autoImplicit false
noncomputable section
local instance : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology
local instance : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

private def homogeneousSwap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 1, v 0]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

private theorem homogeneousSwap_injective : Function.Injective homogeneousSwap := by
  intro v w h
  have h0 := congrFun h 1
  have h1 := congrFun h 0
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The ordinary homogeneous coordinate exchange `[x:y] ↦ [y:x]`. -/
def projectiveLineFlip : ProjectiveLine → ProjectiveLine :=
  Projectivization.map homogeneousSwap homogeneousSwap_injective

theorem projectiveLineFlip_affine (z : ℂ) :
    projectiveLineFlip (affineLinePoint z) = reciprocalLinePoint z := by
  simp only [projectiveLineFlip, affineLinePoint, Projectivization.map_mk]
  rfl

theorem projectiveLineFlip_reciprocal (z : ℂ) :
    projectiveLineFlip (reciprocalLinePoint z) = affineLinePoint z := by
  simp only [projectiveLineFlip, reciprocalLinePoint, Projectivization.map_mk]
  rfl

theorem projectiveLineFlip_involutive : Function.Involutive projectiveLineFlip := by
  intro p
  rcases projectiveLine_chart_cover p with ⟨z, rfl⟩ | ⟨z, rfl⟩ <;>
    simp only [projectiveLineFlip_affine, projectiveLineFlip_reciprocal]

def projectiveFlipFirst (p : ProjectiveLine × ProjectiveLine) :=
  (projectiveLineFlip p.1, p.2)

theorem projectiveAtlas_continuous_iff (f : (ProjectiveLine × ProjectiveLine) →
    ProjectiveLine × ProjectiveLine) :
    Continuous f ↔ ∀ i, Continuous (f ∘ projectiveChart i) := by
  rw [continuous_coinduced_dom, continuous_sigma_iff]
  rfl

theorem projectiveFlipFirst_continuous : Continuous projectiveFlipFirst := by
  apply (projectiveAtlas_continuous_iff _).mpr
  intro i
  fin_cases i
  · exact projectiveChart_continuous 1 |>.congr (fun v => by
      simp [projectiveChart, projectiveFlipFirst,
        affineProjectiveChart, mixedProjectiveChart, projectiveLineFlip_affine])
  · exact projectiveChart_continuous 0 |>.congr (fun v => by
      simp [projectiveChart, projectiveFlipFirst,
        affineProjectiveChart, mixedProjectiveChart, projectiveLineFlip_reciprocal])
  · exact ((projectiveChart_continuous 3).comp exchangeCoordinates_continuous).congr
      (fun v => by simp [projectiveChart, projectiveFlipFirst,
        otherMixedProjectiveChart, reciprocalProjectiveChart, exchangeCoordinates,
        projectiveLineFlip_affine])
  · exact ((projectiveChart_continuous 2).comp exchangeCoordinates_continuous).congr
      (fun v => by simp [projectiveChart, projectiveFlipFirst,
        otherMixedProjectiveChart, reciprocalProjectiveChart, exchangeCoordinates,
        projectiveLineFlip_reciprocal])

def projectiveFlipFirstHomeomorph :
    (ProjectiveLine × ProjectiveLine) ≃ₜ (ProjectiveLine × ProjectiveLine) where
  toFun := projectiveFlipFirst
  invFun := projectiveFlipFirst
  left_inv p := Prod.ext (projectiveLineFlip_involutive p.1) rfl
  right_inv p := Prod.ext (projectiveLineFlip_involutive p.1) rfl
  continuous_toFun := projectiveFlipFirst_continuous
  continuous_invFun := projectiveFlipFirst_continuous

/-- Factor exchange is continuous for the atlas topology, without assuming
that it is a product topology (which would be wrong for Zariski geometry). -/
theorem projectiveFactorSwap_continuous :
    Continuous (Prod.swap : ProjectiveLine × ProjectiveLine → _) := by
  apply (projectiveAtlas_continuous_iff _).mpr
  intro i
  fin_cases i
  · exact ((projectiveChart_continuous 0).comp exchangeCoordinates_continuous).congr
      (fun _ => rfl)
  · exact (projectiveChart_continuous 2).congr (fun _ => rfl)
  · exact (projectiveChart_continuous 1).congr (fun _ => rfl)
  · exact ((projectiveChart_continuous 3).comp exchangeCoordinates_continuous).congr
      (fun _ => rfl)

def projectiveFactorSwapHomeomorph :
    (ProjectiveLine × ProjectiveLine) ≃ₜ (ProjectiveLine × ProjectiveLine) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := projectiveFactorSwap_continuous
  continuous_invFun := projectiveFactorSwap_continuous

theorem mixedProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding mixedProjectiveChart := by
  have h := projectiveFlipFirstHomeomorph.isOpenEmbedding.comp
    affineProjectiveChart_isOpenEmbedding
  have he : projectiveFlipFirstHomeomorph ∘ affineProjectiveChart = mixedProjectiveChart := by
    funext v
    simp [projectiveFlipFirstHomeomorph, projectiveFlipFirst,
      affineProjectiveChart, mixedProjectiveChart, projectiveLineFlip_affine]
  rwa [he] at h

theorem otherMixedProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding otherMixedProjectiveChart :=
  projectiveFactorSwapHomeomorph.isOpenEmbedding.comp mixedProjectiveChart_isOpenEmbedding

theorem reciprocalProjectiveChart_isOpenEmbedding :
    Topology.IsOpenEmbedding reciprocalProjectiveChart := by
  have h := projectiveFlipFirstHomeomorph.isOpenEmbedding.comp
    (otherMixedProjectiveChart_isOpenEmbedding.comp coordinateExchangeHomeomorph.isOpenEmbedding)
  have he : projectiveFlipFirstHomeomorph ∘
      (otherMixedProjectiveChart ∘ coordinateExchangeHomeomorph) = reciprocalProjectiveChart := by
    funext v
    simp [Function.comp_def, projectiveFlipFirstHomeomorph, projectiveFlipFirst,
      otherMixedProjectiveChart, reciprocalProjectiveChart, coordinateExchangeHomeomorph,
      exchangeCoordinates, projectiveLineFlip_affine]
  rwa [he] at h

theorem projectiveChart_isOpenEmbedding (i : Fin 4) :
    Topology.IsOpenEmbedding (projectiveChart i) := by
  fin_cases i
  · exact affineProjectiveChart_isOpenEmbedding
  · exact mixedProjectiveChart_isOpenEmbedding
  · exact otherMixedProjectiveChart_isOpenEmbedding
  · exact reciprocalProjectiveChart_isOpenEmbedding

#print axioms mixedProjectiveChart_isOpenEmbedding
#print axioms otherMixedProjectiveChart_isOpenEmbedding
#print axioms reciprocalProjectiveChart_isOpenEmbedding
#print axioms projectiveChart_isOpenEmbedding

end
end CurveSymmetry
