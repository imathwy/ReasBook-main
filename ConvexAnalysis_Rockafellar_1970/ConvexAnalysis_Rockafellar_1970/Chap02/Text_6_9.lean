import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Short intrinsic-closure notation used in this item's theorem surfaces. -/
local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 6.9 records the immediate inclusion chain between the relative interior,
  the set itself, and its closure.
- `core/canonical`: the intrinsic owner chain is
  `intrinsicInterior_subset` and `subset_intrinsicClosure`.
- `bridge/view`: ambient closure is a downstream bridge from the intrinsic owner layer, with
  `subset_closure` retained as the textbook ambient companion.
- Primitive data vs derived API: this item introduces no data; it only recalls canonical facts
  about `intrinsicInterior`, `intrinsicClosure`, and `closure`.
- Domain-style sampling used here: `intrinsicInterior`, `intrinsicClosure`, `closure`,
  `intrinsicInterior_subset`, `subset_intrinsicClosure`, and `subset_closure`.
- Layer target: the main labeled entries are `core/canonical`.
-/

section

variable
    {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {P : Type*} [TopologicalSpace P] [AddTorsor V P]

/- Text 6.9 (1): the relative interior inclusion `ri C ⊆ C` is exactly the canonical owner theorem
`intrinsicInterior_subset`. -/
recall intrinsicInterior_subset
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] {C : Set P} :
    ri[𝕜](C) ⊆ C

/- Text 6.9 (2), canonical relative-topology layer: the set inclusion into relative closure is the
canonical owner theorem `subset_intrinsicClosure`. -/
recall subset_intrinsicClosure
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] {C : Set P} :
    C ⊆ cl[𝕜](C)

/-- Canonical chain form of Text 6.9 at the intrinsic layer: relative interior is contained in
relative closure. -/
theorem ri_subset_intrinsicClosure
    (C : Set P) :
    ri[𝕜](C) ⊆ cl[𝕜](C) :=
  (intrinsicInterior_subset : ri[𝕜](C) ⊆ C).trans
    (subset_intrinsicClosure : C ⊆ cl[𝕜](C))

/- Bridge from the intrinsic closure layer to ambient closure. -/
recall intrinsicClosure_subset_closure
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] {C : Set P} :
    cl[𝕜](C) ⊆ closure C

/- Text 6.9 bridge companion: chaining the intrinsic inclusion with
`intrinsicClosure_subset_closure` yields the textbook ambient inclusion `ri C ⊆ closure C`. -/
theorem ri_subset_closure (C : Set P) :
    ri[𝕜](C) ⊆ closure C :=
  (ri_subset_intrinsicClosure (𝕜 := 𝕜) C).trans
    (intrinsicClosure_subset_closure (𝕜 := 𝕜) (s := C))

/- Ambient-closure bridge for the textbook surface `C ⊆ cl C`. -/
recall subset_closure

end
