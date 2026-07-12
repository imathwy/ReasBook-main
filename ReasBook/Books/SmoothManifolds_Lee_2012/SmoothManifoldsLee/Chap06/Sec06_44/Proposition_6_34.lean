import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Connected.PathConnected
import SmoothManifolds_Lee_2012.Chap06.Sec06_44.Definition_6_44_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

universe u𝕜 uM uHM uEM uS uHS uES uN uHN uEN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]

variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {I : ModelWithCorners 𝕜 EM HM} [IsManifold I ⊤ M]

variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace 𝕜 ES]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {S : Type uS} [TopologicalSpace S] [ChartedSpace HS S]
variable {J : ModelWithCorners 𝕜 ES HS} [IsManifold J ⊤ S]

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {K : ModelWithCorners 𝕜 EN HN} [IsManifold K ⊤ N]

-- Domain sampling pass: the source-facing owner for smooth families in Section 6.44 is
-- `IsSmoothFamily`, while the canonical core remains `ContMDiff` on the uncurried map and bundled
-- smooth maps appear only as derived slices or coercions to `ContinuousMap`.
-- Relevant canonical declarations checked before refinement:
-- `IsSmoothFamily`,
-- `ChartedSpace.locPathConnectedSpace`,
-- `ModelWithCorners.convex_range`,
-- `PathConnectedSpace.of_locPathConnectedSpace`.

/-- A charted manifold modeled on a space with corners over an `IsRCLikeNormedField` is locally
path-connected. -/
private theorem chartedSpace_locPathConnectedSpace (J : ModelWithCorners 𝕜 ES HS) :
    LocPathConnectedSpace S := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ ES := NormedSpace.restrictScalars ℝ 𝕜 ES
  letI : LocPathConnectedSpace HS := by
    letI : LocPathConnectedSpace (Set.range J) := J.convex_range.locPathConnectedSpace
    let e : HS ≃ₜ Set.range J := J.isClosedEmbedding.toHomeomorph
    exact e.isOpenEmbedding.locPathConnectedSpace
  exact ChartedSpace.locPathConnectedSpace HS S

/- Proposition 6.34: if `F` is a smooth family of maps from `N` to `M` parametrized by a
connected manifold `S`, then any two fibers of the family are homotopic. -/
variable [ConnectedSpace S]

omit [IsManifold I ⊤ M] [IsManifold J ⊤ S] [IsManifold K ⊤ N] in theorem
    smooth_family_slices_homotopic
    {F : S → N → M} (hF : IsSmoothFamily I J K F) (s₁ s₂ : S) :
    (hF.slice s₁ : C(N, M)).Homotopic (hF.slice s₂ : C(N, M)) := by
  letI : LocPathConnectedSpace S := chartedSpace_locPathConnectedSpace J
  letI : PathConnectedSpace S := PathConnectedSpace.of_locPathConnectedSpace
  let γ : Path s₁ s₂ := PathConnectedSpace.somePath s₁ s₂
  have hγ : Continuous fun p : Set.Icc (0 : ℝ) 1 × N ↦ (γ p.1, p.2) :=
    (γ.continuous.comp continuous_fst).prodMk continuous_snd
  have hcontF : Continuous (Function.uncurry F) := hF.contMDiff.continuous
  refine ⟨{
    toFun := fun p ↦ F (γ p.1) p.2
    continuous_toFun := hcontF.comp hγ
    map_zero_left := ?_
    map_one_left := ?_
  }⟩
  · intro x
    simp [IsSmoothFamily.slice, γ.source]
  · intro x
    simp [IsSmoothFamily.slice, γ.target]
