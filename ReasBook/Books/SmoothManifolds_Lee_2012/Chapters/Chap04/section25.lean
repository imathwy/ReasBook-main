import Mathlib
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_25_extra_1 (from Chap04/Sec04_25) -/
universe u v

open TopologicalSpace

namespace ContinuousMap

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/- Definition 4.25-extra-1 (1): a section of a bundled continuous map `π : C(M, N)` is exactly a
continuous right inverse `σ : C(N, M)`, expressed by the canonical owner
`Function.RightInverse σ π`. -/
recall Function.RightInverse

variable (π : C(M, N)) (U : TopologicalSpace.Opens N) (σ : C(U, M))

/- Definition 4.25-extra-1 (2): a local section of a continuous map `π : C(M, N)` over an open
subset `U` of the base is a continuous map `σ : C(U, M)` whose composite with `π` is the
inclusion `U → N`. -/
def IsLocalSection : Prop :=
  ∀ x : U, π (σ x) = x

namespace IsLocalSection

/-- A local section satisfies the section equation at each point of its open domain. -/
theorem apply_eq {π : C(M, N)} {U : Opens N} {σ : C(U, M)} (hσ : π.IsLocalSection U σ)
    (x : U) : π (σ x) = x := by
  exact hσ x

end IsLocalSection

end ContinuousMap

namespace Function.RightInverse

open ContinuousMap TopologicalSpace

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]

/-- A global section restricts to a local section on the whole target. -/
theorem isLocalSection_restrict_top {π : C(M, N)} {σ : C(N, M)}
    (hσ : Function.RightInverse σ π) :
    π.IsLocalSection ⊤ (σ.restrict (⊤ : Set N)) := by
  intro x
  simpa using hσ.eq (x : N)

end Function.RightInverse

/-! ### Definition_4_25_extra_2 (from Chap04/Sec04_25) -/
universe u v

namespace Topology

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Definition 4.25-extra-2: A topological submersion is a continuous map such that every point of
the source lies on a continuous local section through its image. -/
@[mk_iff]
structure IsTopologicalSubmersion (π : X → Y) : Prop where
  /-- A topological submersion is continuous. -/
  continuous : Continuous π
  /-- Every source point lies on a continuous local section defined near its image. -/
  local_section (x : X) :
    ∃ U : TopologicalSpace.Opens Y, ∃ hxU : π x ∈ U, ∃ σ : C(U, X),
      (⟨π, continuous⟩ : C(X, Y)).IsLocalSection U σ ∧ σ ⟨π x, hxU⟩ = x

namespace IsTopologicalSubmersion

variable {π : X → Y}

/-- A topological submersion is continuous. -/
instance (hπ : IsTopologicalSubmersion π) : Continuous π := hπ.continuous

/-- A topological submersion is an open map. -/
-- Proof sketch: let `W ⊆ X` be open and `y ∈ π '' W`, choose `x ∈ W` with `π x = y`, and use the
-- local section through `x` to produce an open neighborhood of `y` contained in `π '' W`.
theorem isOpenMap (hπ : IsTopologicalSubmersion π) : IsOpenMap π := by
  intro W hW
  rw [isOpen_iff_mem_nhds]
  intro y hy
  rcases hy with ⟨x, hxW, rfl⟩
  rcases hπ.local_section x with ⟨U, hxU, σ, hσ, hσx⟩
  let V : Set U := σ ⁻¹' W
  have hV : IsOpen V := hW.preimage σ.continuous
  have hV_image : IsOpen (((↑) : U → Y) '' V) := U.2.isOpenMap_subtype_val V hV
  have hV_subset : ((↑) : U → Y) '' V ⊆ π '' W := by
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨σ u, hu, ContinuousMap.IsLocalSection.apply_eq hσ u⟩
  have hy_image : π x ∈ ((↑) : U → Y) '' V := by
    refine ⟨⟨π x, hxU⟩, ?_, rfl⟩
    simpa [V, hσx] using hxW
  exact Filter.mem_of_superset (hV_image.mem_nhds hy_image) hV_subset

/-- A surjective topological submersion is a quotient map. -/
theorem isQuotientMap (hπ : IsTopologicalSubmersion π) (h_surj : Function.Surjective π) :
    IsQuotientMap π :=
  hπ.isOpenMap.isQuotientMap hπ.continuous h_surj

end IsTopologicalSubmersion

end Topology

namespace IsLocalHomeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}

/-- A local homeomorphism is a topological submersion. -/
-- Proof sketch: For each `x`, choose an open partial homeomorphism `e` agreeing with `π` on a
-- neighborhood of `x`. Then `e.target` is an open neighborhood of `π x`, and `e.symm` is a
-- continuous local section of `π` on that neighborhood sending `π x` back to `x`.
theorem isTopologicalSubmersion (hπ : IsLocalHomeomorph π) :
    Topology.IsTopologicalSubmersion π := by
  refine
    { continuous := hπ.continuous
      local_section := ?_ }
  intro x
  let e := hπ.localInverseAt x
  let U : TopologicalSpace.Opens Y := ⟨e.source, e.open_source⟩
  let σ : C(U, X) :=
    ⟨Set.restrict e.source e,
      continuousOn_iff_continuous_restrict.mp e.continuousOn⟩
  have hxU : π x ∈ U := by
    change π x ∈ e.source
    exact hπ.apply_self_mem_localInverseAt_source
  refine ⟨U, hxU, σ, ?_, ?_⟩
  · intro y
    change π (e y) = y
    exact hπ.apply_localInverseAt_of_mem y.2
  · change e (π x) = x
    exact hπ.localInverseAt_apply_self

end IsLocalHomeomorph

/-! ### Theorem_4_25 (from Chap04/Sec04_24) -/
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local chapter
-- precedents and mathlib's `Manifold.IsImmersion` / `Manifold.IsSmoothEmbedding` APIs were
-- inspected directly.

open scoped ContDiff Manifold

namespace Manifold

section

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- Theorem 4.25 (Local Embedding Theorem): a smooth map is a smooth immersion if and only if
every point of the source has an open neighborhood on which the restricted map is a smooth
embedding. -/
theorem isImmersion_iff_forall_exists_open_restriction_isSmoothEmbedding {F : M → N} :
    IsImmersion I J ∞ F ↔
      ∀ p : M, ∃ U : TopologicalSpace.Opens M, p ∈ U ∧
        IsSmoothEmbedding I J ∞ (F ∘ (Subtype.val : U → M)) := sorry

end

end Manifold
