import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.Sets.OpenCover
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/- Domain-style sampling:
- primary domain: open covers and locally finite families of subsets in a topological space
- same-domain declarations inspected:
  `TopologicalSpace.IsOpenCover`,
  `TopologicalSpace.IsOpenCover.exists_mem`,
  `LocallyFinite`,
  `LocallyFinite.exists_mem_basis`
- owner abstractions: `TopologicalSpace.IsOpenCover` for the covering condition and
  `LocallyFinite` for the local-finiteness condition
  There is no single upstream bundled owner for “locally finite open cover”, so the faithful
  canonical surface here is the conjunction of these two owner predicates rather than a new local
  wrapper.

Layer triage:
- `source-facing`: a locally finite open cover
- `core/canonical`: the pair `IsOpenCover U` and `LocallyFinite (Opens.asSets U)`
- `bridge/view`: the open-neighborhood formulation specialized from
  `LocallyFinite.exists_mem_basis`

Primitive data are exactly the covering condition and the locally finite family of underlying
subsets. The previous local wrapper duplicated both owner notions as primitive fields, and its
neighborhood lemma actually depended only on `LocallyFinite`. This file should therefore expose
the canonical owners directly instead of maintaining a parallel bundled class. -/

namespace TopologicalSpace

namespace Opens

/-- A family of open subsets, viewed as the corresponding family of subsets. -/
abbrev asSets (U : ι → Opens X) : ι → Set X := fun i ↦ U i

/-- Two open subsets meet if their underlying subsets are not disjoint. -/
abbrev Meets (U V : Opens X) : Prop := ¬ Disjoint (U : Set X) (V : Set X)

/-- Open subsets meet exactly when they share a point. -/
theorem meets_iff {U V : Opens X} : U.Meets V ↔ ∃ x, x ∈ U ∧ x ∈ V := by
  simpa [Meets] using
    (Set.not_disjoint_iff_nonempty_inter : ¬ Disjoint (U : Set X) (V : Set X) ↔
      ((U : Set X) ∩ (V : Set X)).Nonempty)

end Opens

variable (U : ι → Opens X)

/- Definition 20.24.2: since the project and mathlib expose no separate bundled owner for a
locally finite open cover, the canonical source-faithful entry is the conjunction of the open-cover
owner and the locally finite-family owner. -/
#check (IsOpenCover U ∧ LocallyFinite (Opens.asSets U))

end TopologicalSpace

/- Source-facing bridge: the neighborhood-basis formulation of local finiteness for open subsets is
already the canonical theorem `LocallyFinite.exists_mem_basis`, specialized using
`nhds_basis_opens' x`. This file recalls that owner-level bridge directly instead of maintaining a
parallel local reformulation. -/
recall LocallyFinite.exists_mem_basis

namespace LocallyFinite

open TopologicalSpace.Opens

/-- For a locally finite family of open subsets, every point of an open `V` admits a smaller open
subset of `V` that meets only finitely many members of the family. This is the source-facing open
neighborhood form used in Remark 20.24.3, packaged as a thin bridge around
`LocallyFinite.exists_mem_basis`. -/
theorem exists_open_le_with_finite_nonempty_inter
    {U : ι → Opens X} (hU : LocallyFinite (asSets U))
    (V : Opens X) {x : X} (hx : x ∈ V) :
    ∃ W : Opens X, x ∈ W ∧ W ≤ V ∧
      {i | W.Meets (U i)}.Finite := by
  obtain ⟨s, hs, hsfinite⟩ := hU.exists_mem_basis (nhds_basis_opens' x)
  rcases hs with ⟨hxs, hsopen⟩
  let W : Opens X := ⟨s ∩ V, hsopen.inter V.isOpen⟩
  refine ⟨W, ?_, ?_, ?_⟩
  · exact ⟨hsopen.mem_nhds_iff.mp hxs, hx⟩
  · exact fun y hy ↦ hy.2
  · refine hsfinite.subset ?_
    intro i hi
    rcases meets_iff.mp hi with ⟨y, hyW, hyU⟩
    exact ⟨y, hyU, hyW.1⟩

end LocallyFinite

namespace TopologicalSpace

open Opens

/-- Definition 20.24.2 (Tag 02FS): an indexed open cover is locally finite exactly when each point
admits an open neighborhood meeting only finitely many members of the family. The open-cover
condition itself remains the canonical owner `IsOpenCover U`, while local finiteness is expressed
through `LocallyFinite (asSets U)`. -/
@[stacks 02FS]
theorem locallyFiniteCover_iff (U : ι → Opens X) :
    (IsOpenCover U ∧ LocallyFinite (asSets U)) ↔
      IsOpenCover U ∧ ∀ x : X, ∃ W : Opens X, x ∈ W ∧ {i | W.Meets (U i)}.Finite := by
  constructor
  · rintro ⟨hcover, hlf⟩
    refine ⟨hcover, ?_⟩
    intro x
    obtain ⟨W, hxW, -, hWfinite⟩ :=
      LocallyFinite.exists_open_le_with_finite_nonempty_inter hlf ⊤ (by simp)
    exact ⟨W, hxW, hWfinite⟩
  · rintro ⟨hcover, hlocal⟩
    refine ⟨hcover, (locallyFinite_iff_smallSets.2 ?_)⟩
    intro x
    rcases hlocal x with ⟨W, hxW, hWfinite⟩
    refine Filter.eventually_smallSets.2 ?_
    refine ⟨(W : Set X), W.isOpen.mem_nhds hxW, ?_⟩
    intro t ht
    refine hWfinite.subset ?_
    intro i hi
    rcases hi with ⟨y, hyUi, hyt⟩
    exact Opens.meets_iff.mpr ⟨y, ht hyt, hyUi⟩

end TopologicalSpace
