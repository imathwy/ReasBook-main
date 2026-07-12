import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Exercise_4_10
import SmoothManifolds_Lee_2012.Chap07.Sec07_50.Definition_7_50_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_50.Definition_7_50_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uVE uHE uVM uHM

section CoveringAutomorphismGroup

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace 𝕜 VE]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {E : Type*} [TopologicalSpace E] [ChartedSpace HE E]
variable {M : Type*}
variable {I : ModelWithCorners 𝕜 VE HE} [IsManifold I ∞ E]
variable {π : E → M}

-- `lean_leansearch` was unavailable in this environment; the statement surface below was verified
-- directly against the local `coveringAutomorphismGroup` owner and mathlib's `LieGroup`,
-- `ContMDiffSMul`, and `IsCancelSMul` APIs.

local notation "I0" => modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin 0))

namespace CoveringAutomorphismGroup

local notation "Autπ" => coveringAutomorphismGroup π

instance instTopologicalSpace : TopologicalSpace Autπ :=
  ⊥

instance instDiscreteTopology : DiscreteTopology Autπ :=
  ⟨rfl⟩

instance instChartedSpace : ChartedSpace (EuclideanSpace 𝕜 (Fin 0)) Autπ :=
  ChartedSpace.of_discreteTopology

instance instIsManifold : IsManifold I0 ∞ Autπ := by
  show IsManifold (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin 0))) ∞ Autπ
  exact IsManifold.of_discreteTopology ∞

instance instLieGroup : LieGroup I0 ∞ Autπ where
  contMDiff_mul := by
    have hmul :
        ContMDiff
          ((modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin 0))).prod
            (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin 0))))
          (modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin 0)))
          ∞
          (fun p : Autπ × Autπ ↦ p.1 * p.2) :=
      contMDiff_of_discreteTopology
    simpa using hmul
  contMDiff_inv := by
    have hinv : ContMDiff I0 I0 ∞ (fun g : Autπ ↦ g⁻¹) :=
      contMDiff_of_discreteTopology
    simpa using hinv

end CoveringAutomorphismGroup

/-- Companion to Proposition 7.23 (1): with the discrete topology, the covering automorphism
group `Aut_π(E) = coveringAutomorphismGroup π` is discrete. -/
theorem coveringAutomorphismGroup_discreteTopology :
    DiscreteTopology (coveringAutomorphismGroup π) :=
  inferInstance

/-- Companion to Proposition 7.23 (2): with the discrete topology, the covering automorphism
group `Aut_π(E) = coveringAutomorphismGroup π` is a zero-dimensional Lie group. -/
theorem coveringAutomorphismGroup_lieGroup :
    LieGroup I0 ∞ (coveringAutomorphismGroup π) :=
  inferInstance

section SmoothCovering

variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace 𝕜 VM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners 𝕜 VM HM} [IsManifold J ∞ M]

/-- Helper for Proposition 7.23: each covering automorphism acts continuously on `E` because it is
the underlying self-homeomorphism. -/
instance coveringAutomorphismGroup_continuousConstSMul :
    ContinuousConstSMul (coveringAutomorphismGroup π) E where
  continuous_const_smul := by
    intro φ
    -- The action by a fixed deck transformation is evaluation by a homeomorphism.
    simpa [coveringAutomorphismGroup_smul_def] using (φ : E ≃ₜ E).continuous

/-- Helper for Proposition 7.23: the discrete covering automorphism group acts continuously on
`E`. -/
instance coveringAutomorphismGroup_continuousSMul :
    ContinuousSMul (coveringAutomorphismGroup π) E where
  continuous_smul := by
    -- A map out of a discrete left factor is continuous once each scalar action is continuous.
    show Continuous (fun p : coveringAutomorphismGroup π × E ↦ p.1 • p.2)
    exact continuous_prod_of_discrete_left.mpr continuous_const_smul

omit [TopologicalSpace M] in
/-- Helper for Proposition 7.23: deck transformations preserve the covering map pointwise. -/
theorem coveringAutomorphismGroup_pi_smul
    (φ : coveringAutomorphismGroup π) (x : E) :
    π (φ • x) = π x := by
  -- Evaluate the defining equation `π ∘ φ = π` at `x`.
  simpa [coveringAutomorphismGroup_smul_def] using congrFun φ.2 x

omit [IsManifold I ∞ E] [IsManifold J ∞ M] in
/-- Proposition 7.23: for a smooth covering map `π`, the covering automorphism group acts
smoothly on the total space `E`. -/
theorem coveringAutomorphismGroup_contMDiffSMul
    (hπ : Manifold.IsSmoothCoveringMap I J π) :
    ContMDiffSMul I0 I ∞ (coveringAutomorphismGroup π) E := by
  refine ⟨?_⟩
  let μ : coveringAutomorphismGroup π × E → E := fun p ↦ p.1 • p.2
  have hμContinuous : Continuous μ := continuous_smul
  have hcomp : π ∘ μ = π ∘ Prod.snd := by
    -- The action map becomes the projection after composing with the covering map.
    ext p
    exact coveringAutomorphismGroup_pi_smul (π := π) p.1 p.2
  -- Smoothness of the action is detected after composing with the smooth local diffeomorphism `π`.
  refine (smooth_iff_comp_left_of_isLocalDiffeomorph hπ.isLocalDiffeomorph hμContinuous).mpr ?_
  -- After the normalization above, the composite is just `π` after the second projection.
  simpa [μ, hcomp] using
    (hπ.isLocalDiffeomorph.contMDiff.comp
      (contMDiff_snd :
        ContMDiff ((modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin 0))).prod I) I ∞
          (Prod.snd : coveringAutomorphismGroup π × E → E)))

end SmoothCovering

section TopologicalCovering

variable [TopologicalSpace M] [PreconnectedSpace E]

/-- Companion to Proposition 7.23 (4): for a covering map `π` with preconnected total space `E`,
the covering automorphism group acts freely on `E`. -/
theorem coveringAutomorphismGroup_isFree
    (hπ : IsCoveringMap π) :
    IsCancelSMul (coveringAutomorphismGroup π) E := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro φ x hx
  apply Subtype.ext
  ext y
  let hφ : (φ : E → E) = id :=
    hπ.eq_of_comp_eq (φ : E ≃ₜ E).continuous continuous_id
      (show π ∘ (φ : E → E) = π from φ.2) x <|
      by simpa [coveringAutomorphismGroup_smul_def] using hx
  exact congrFun hφ y

end TopologicalCovering

end CoveringAutomorphismGroup
