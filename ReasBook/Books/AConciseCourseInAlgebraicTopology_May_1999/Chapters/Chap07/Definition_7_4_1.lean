import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Sets.OpenCover

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Bundle

variable {E : Type u} {B : Type v} {F : Type w}
variable [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F]

-- Mathlib's canonical core owner is `FiberBundle` for the projection `π F E` of a dependent
-- family. Definition 7.4.1 is source-facing for an arbitrary map `p : E → B`, so we keep the
-- local-triviality predicate on `p` and bridge to `FiberBundle` below.

/-- Definition 7.4.1: a bundle map `p : E → B` with fiber `F` is locally isomorphic over an open
cover to the projections `U × F → U` when every `b : B` lies in the base set of some
`Trivialization F p`. -/
def IsFiberBundleMap (F : Type w) [TopologicalSpace F] (p : E → B) : Prop :=
  ∀ b : B, ∃ e : Trivialization F p, b ∈ e.baseSet

namespace IsFiberBundleMap

variable {p : E → B}

/-- A fiber bundle map admits a local trivialization around each base point. -/
theorem exists_trivializationAt (h : IsFiberBundleMap F p) (b : B) :
    ∃ e : Trivialization F p, b ∈ e.baseSet :=
  h b

/-- The base sets of all local trivializations form an open cover. -/
theorem isOpenCover_baseSet (h : IsFiberBundleMap F p) :
    TopologicalSpace.IsOpenCover (fun e : Trivialization F p ↦ ⟨e.baseSet, e.open_baseSet⟩) := by
  refine TopologicalSpace.IsOpenCover.of_sets (fun e ↦ e.open_baseSet) ?_
  ext b
  constructor
  · intro _
    simp
  · intro _
    obtain ⟨e, hb⟩ := h b
    exact Set.mem_iUnion.2 ⟨e, hb⟩

/-- The pointwise local-triviality condition is equivalent to saying that the trivialization base
sets form an open cover of `B`. -/
theorem iff_isOpenCover_baseSet (p : E → B) :
    IsFiberBundleMap F p ↔
      TopologicalSpace.IsOpenCover (fun e : Trivialization F p ↦ ⟨e.baseSet, e.open_baseSet⟩) := by
  constructor
  · exact isOpenCover_baseSet
  · intro h b
    obtain ⟨e, hb⟩ := h.exists_mem b
    exact ⟨e, hb⟩

end IsFiberBundleMap

namespace FiberBundle

variable (Z : B → Type u) [TopologicalSpace (TotalSpace F Z)] [∀ b, TopologicalSpace (Z b)]
variable [FiberBundle F Z]

/-- The projection of a fiber bundle is a bundle map in the sense of Definition 7.4.1. -/
theorem isFiberBundleMap : IsFiberBundleMap F (π F Z) := fun b ↦
  ⟨trivializationAt F Z b, mem_baseSet_trivializationAt F Z b⟩

end FiberBundle

/-- The local pointwise formulation of `IsFiberBundleMap` is equivalent to the existence of a
family of trivializations whose base sets cover `B`. -/
theorem isFiberBundleMap_iff_exists_open_cover (p : E → B) :
    IsFiberBundleMap F p ↔
      ∃ O : Set (Trivialization F p), ∀ b : B, ∃ e ∈ O, b ∈ e.baseSet := by
  constructor
  · intro h
    refine ⟨Set.univ, ?_⟩
    intro b
    obtain ⟨e, hb⟩ := h b
    exact ⟨e, Set.mem_univ e, hb⟩
  · rintro ⟨O, hCover⟩ b
    obtain ⟨e, _, hb⟩ := hCover b
    exact ⟨e, hb⟩
