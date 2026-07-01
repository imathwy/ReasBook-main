import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.3 gives textbook terminology for vectors lying in the lineality
  space of `C`.
- `core/canonical`: in this chapter's local API, the owner object is the short canonical
  scalar-parameterized set owner `Set.lineal 𝕜 C`, written on theorem surfaces as `lin[𝕜](C)`.
- `bridge/view`: the relevant companion APIs are the canonical owner-membership bridge
  `Set.mem_lineal_iff_mem_recessionCone`, the canonical
  element-level compatibility bridge `Set.mem_lineal_iff`, its source-order compatibility view
  `Set.mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone`, and the textbook quantifier
  form `Set.mem_lineal_iff_forall`.
- Primitive data vs derived API: this item adds no new primitive data beyond the owner set from
  Definition 8.4.2, so it should be a direct recall/use of that owner rather than a parallel
  predicate alias.
- Layer target: this file stays `source-facing`, but only as terminology attached to the existing
  owner declaration.

Domain-style sampling used here:
- the immediately upstream owner `Set.lineal` from Definition 8.4.2;
- its canonical element-level membership bridge `Set.mem_lineal_iff_mem_recessionCone`;
- its canonical membership bridge `Set.mem_lineal_iff`;
- its source-order compatibility bridge
  `Set.mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone`;
- the textbook quantifier expansion `Set.mem_lineal_iff_forall`.
- this numbered item only recalls owner terminology from Definition 8.4.2, so its canonical
  surface lives on the minimal scalar-parameterized additive layer.
-/

/- Definition 8.4.3: a vector is a direction in which `C` is linear precisely when it belongs to
the previously defined owner set `lin[𝕜](C)` (that is, `Set.lineal 𝕜 C`). -/
recall Set.lineal

/- The canonical element-level membership bridge: membership in `lin[𝕜](C)` means both `y`
and `-y` are recession directions of `C`. -/
recall Set.mem_lineal_iff_mem_recessionCone

/- The textbook wording is unpacked by the standard canonical membership characterization of
`lin[𝕜](C)`. -/
recall Set.mem_lineal_iff

/- Source-order compatibility view used in nearby source-facing statements. -/
recall Set.mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone

/- The fully unpacked source wording is the quantifier form of lineality membership. -/
recall Set.mem_lineal_iff_forall
