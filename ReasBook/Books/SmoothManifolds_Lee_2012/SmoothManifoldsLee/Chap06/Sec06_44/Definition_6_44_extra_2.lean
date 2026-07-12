import Mathlib.Geometry.Manifold.ContMDiffMap

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe u𝕜 uM uHM uEM uS uHS uES uN uHN uEN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]

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

-- Domain sampling pass: this file lies in the smooth-family / smooth-homotopy domain.
-- Relevant owner declarations checked before refinement:
-- `ContMDiff` on product manifolds,
-- `ContMDiff.curry_left`,
-- `ContMDiff.curry_right`,
-- and bundled smooth maps `ContMDiffMap`.
-- Layer triage:
-- * source-facing: `IsSmoothFamily`
-- * core/canonical: `ContMDiff (J.prod K) I ∞ (Function.uncurry F)`
-- * bridge/view: bundled `ContMDiffMap` on `S × N` or on individual slices
-- The public API keeps the source-facing family predicate central and derives bundled slices from
-- it instead of presenting bundled maps on `S × N` as a second owner.

/-- Definition 6.44-extra-2: a family of maps `F s : N → M` parametrized by `S` is smooth if its
uncurried map `S × N → M`, `(s, x) ↦ F s x`, is smooth. -/
def IsSmoothFamily (I : ModelWithCorners 𝕜 EM HM) (J : ModelWithCorners 𝕜 ES HS)
    (K : ModelWithCorners 𝕜 EN HN) (F : S → N → M) : Prop :=
  ContMDiff (J.prod K) I ∞ (Function.uncurry F)

/-- A bundled smooth map on `S × N` determines a smooth family of maps `N → M` parametrized by
`S`. -/
instance isSmoothFamily_of_bundledSmoothMap (F : C^∞⟮J.prod K, S × N; I, M⟯) :
    IsSmoothFamily I J K (Function.curry F) :=
  F.contMDiff

section

omit [IsManifold I ⊤ M] [IsManifold J ⊤ S] [IsManifold K ⊤ N] in
/-- A smooth family has a smooth uncurried evaluation map on `S × N`. -/
theorem IsSmoothFamily.contMDiff {F : S → N → M} (hF : IsSmoothFamily I J K F) :
    ContMDiff (J.prod K) I ∞ (Function.uncurry F) :=
  hF

omit [IsManifold I ⊤ M] [IsManifold J ⊤ S] [IsManifold K ⊤ N] in
/-- Fixing the parameter in a smooth family gives a smooth map `N → M`. -/
theorem IsSmoothFamily.contMDiff_slice {F : S → N → M} (hF : IsSmoothFamily I J K F) (s : S) :
    ContMDiff K I ∞ (F s) :=
  hF.contMDiff.curry_right

omit [IsManifold I ⊤ M] [IsManifold J ⊤ S] [IsManifold K ⊤ N] in
/-- A smooth family canonically determines a bundled smooth slice `N → M` at each parameter. -/
def IsSmoothFamily.slice {F : S → N → M} (hF : IsSmoothFamily I J K F) (s : S) :
    C^∞⟮K, N; I, M⟯ :=
  ⟨F s, hF.contMDiff_slice s⟩

omit [IsManifold I ⊤ M] [IsManifold J ⊤ S] [IsManifold K ⊤ N] in
@[simp] theorem IsSmoothFamily.slice_apply {F : S → N → M} (hF : IsSmoothFamily I J K F) (s : S)
    (x : N) : hF.slice s x = F s x :=
  rfl

end
