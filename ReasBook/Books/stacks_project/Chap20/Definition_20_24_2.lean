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
- `core/canonical`: the pair `IsOpenCover U` and `LocallyFinite fun i ↦ (U i : Set X)`
- `bridge/view`: the open-neighborhood formulation specialized from
  `LocallyFinite.exists_mem_basis`

Primitive data are exactly the covering condition and the locally finite family of underlying
subsets. The previous local wrapper duplicated both owner notions as primitive fields, and its
neighborhood lemma actually depended only on `LocallyFinite`. This file should therefore expose
the canonical owners directly instead of maintaining a parallel bundled class. -/

namespace TopologicalSpace

variable (U : ι → Opens X)

/- Definition 20.24.2: since the project and mathlib expose no separate bundled owner for a
locally finite open cover, the canonical source-faithful entry is the conjunction of the open-cover
owner and the locally finite-family owner. -/
#check (IsOpenCover U ∧ LocallyFinite fun i ↦ (U i : Set X))

end TopologicalSpace

/- Source-facing bridge: the neighborhood-basis formulation of local finiteness for open subsets is
already the canonical theorem `LocallyFinite.exists_mem_basis`, specialized using
`nhds_basis_opens' x`. This file recalls that owner-level bridge directly instead of maintaining a
parallel local reformulation. -/
recall LocallyFinite.exists_mem_basis
