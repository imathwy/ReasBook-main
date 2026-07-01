import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Maps.Proper.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe uK uVE uVM uHE uHM uE uM

section

variable {K : Type uK} [NontriviallyNormedField K]
variable {VE : Type uVE} [NormedAddCommGroup VE] [NormedSpace K VE]
variable {VM : Type uVM} [NormedAddCommGroup VM] [NormedSpace K VM]
variable {HE : Type uHE} [TopologicalSpace HE]
variable {HM : Type uHM} [TopologicalSpace HM]
variable (IE : ModelWithCorners K VE HE) (IM : ModelWithCorners K VM HM)
variable {E : Type uE} [TopologicalSpace E] [ChartedSpace HE E] [T2Space E]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable [Nonempty E] [PreconnectedSpace M]

namespace Manifold

/-- Definition 4.26-extra-1: a smooth covering map is a surjective topological covering map that
is also a smooth local diffeomorphism. This local reintroduction keeps the proposition file
self-contained while the canonical owner file is unavailable. -/
def IsSmoothCoveringMap
    (I : ModelWithCorners K VE HE) (I' : ModelWithCorners K VM HM) (π : E → M) : Prop :=
  IsCoveringMap π ∧ Function.Surjective π ∧ IsLocalDiffeomorph I I' ∞ π

end Manifold

omit [T2Space E] [Nonempty E] [PreconnectedSpace M] in
/-- Helper for Proposition 4.46: a local diffeomorphism provides an open partial homeomorphism
branch through each source point. -/
lemma exists_openPartialHomeomorph_eq_of_localDiffeomorph {π : E → M}
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (e : E) :
    ∃ φ : OpenPartialHomeomorph E M, e ∈ φ.source ∧ φ = π := by
  -- Translate the local-diffeomorphism hypothesis into the local-homeomorphism API used by the
  -- covering criterion.
  obtain ⟨φ, hφ, hπφ⟩ := hlocal.isLocalHomeomorph e
  exact ⟨φ, hφ, hπφ.symm⟩

omit [T2Space E] [Nonempty E] [PreconnectedSpace M] in
/-- Helper for Proposition 4.46: every fiber of a local diffeomorphism is a discrete subset. -/
lemma fiber_is_discrete_of_local_diffeomorph {π : E → M}
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : M) : IsDiscrete (π ⁻¹' {x}) := by
  -- Each point of the fiber lies in a neighborhood where `π` agrees with a local homeomorphism, so
  -- the covering-space discreteness criterion applies directly.
  refine IsDiscrete.of_openPartialHomeomorph π subset_rfl ?_
  intro e he
  exact exists_openPartialHomeomorph_eq_of_localDiffeomorph (IE := IE) (IM := IM) hlocal e

omit [T2Space E] [Nonempty E] [PreconnectedSpace M] in
/-- Helper for Proposition 4.46: properness upgrades the discrete fibers of a local diffeomorphism
to finite fibers. -/
lemma fiber_finite_of_proper_local_diffeomorph {π : E → M} (hproper : IsProperMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) (x : M) : (π ⁻¹' {x}).Finite := by
  -- Proper maps have compact fibers over compact singletons, and compact discrete subsets are
  -- finite.
  refine (hproper.isCompact_preimage isCompact_singleton).finite ?_
  exact fiber_is_discrete_of_local_diffeomorph (IE := IE) (IM := IM) hlocal x

omit [T2Space E] in
/-- Helper for Proposition 4.46: the range of a proper local diffeomorphism is nonempty, open, and
closed, hence equals the whole preconnected target. -/
lemma surjective_of_nonempty_preconnected_open_closed_range {π : E → M} (hproper : IsProperMap π)
    (hlocal : IsLocalDiffeomorph IE IM ∞ π) : Function.Surjective π := by
  -- The range and its complement form an open separation of `M`; preconnectedness forces the
  -- nonempty side containing the range to be all of `M`.
  have hrange : (Set.univ : Set M) ⊆ Set.range π := by
    refine isPreconnected_univ.subset_left_of_subset_union hlocal.isOpen_range
      hproper.isClosed_range.isOpen_compl disjoint_compl_right ?_ ?_
    · intro x
      simp
    · rcases Set.range_nonempty π with ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
  -- Turning the range equality into surjectivity finishes the clopen-image argument.
  rw [← Set.range_eq_univ]
  exact Set.eq_univ_of_univ_subset hrange

/-- Proposition 4.46: a proper smooth local diffeomorphism from a nonempty Hausdorff source to a
preconnected target is a smooth covering map. The source-connectedness hypothesis from the textbook
statement is redundant for this conclusion. -/
theorem isSmoothCoveringMap_of_proper_localDiffeomorph {π : E → M}
    (hproper : IsProperMap π) (hlocal : IsLocalDiffeomorph IE IM ∞ π) :
    Manifold.IsSmoothCoveringMap IE IM π := by
  refine ⟨?_, ⟨?_, hlocal⟩⟩
  · -- The source-proof's evenly-covered neighborhood construction is packaged by the closed-map
    -- covering criterion once we supply finite fibers and local branches.
    rw [isCoveringMap_iff_isCoveringMapOn_univ]
    refine hproper.isClosedMap.isCoveringMapOn_of_openPartialHomeomorph ?_ ?_
    · intro x _
      exact fiber_finite_of_proper_local_diffeomorph (IE := IE) (IM := IM) hproper hlocal x
    · intro e _
      exact exists_openPartialHomeomorph_eq_of_localDiffeomorph
        (IE := IE) (IM := IM) hlocal e
  · -- Surjectivity is the clopen-range argument from the textbook proof.
    exact surjective_of_nonempty_preconnected_open_closed_range
      (IE := IE) (IM := IM) hproper hlocal

end
