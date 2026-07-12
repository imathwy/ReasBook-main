import Mathlib.Tactic.Recall
import Mathlib.Analysis.Convex.Exposed
import ConvexAnalysis_Rockafellar_1970.Chap04.Defn_18_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage:
- `source-facing`: the item says that a face of `C` remains a face in any intermediate set `D`,
  and that an exposed face of `C` remains exposed in such a `D`.
- `core/canonical`: the source-facing owner for faces is `Set.IsFace`, and exposed faces are owned
  by `IsExposed`.
- `bridge/view`: clause (1) is exactly `Set.IsFace.mono`, surfaced here both in owner form and in
  the chapter face-family notation `𝓕[R](C)`. Clause (2) is the canonical owner monotonicity of
  `IsExposed`, namely `IsExposed.mono`.

Domain-style sampling used here:
- `Set.IsFace.mono`;
- `Set.IsFace.mem_faces_mono`;
- `IsExposed.mono`;
- `IsExtreme.subset`;
- `IsExposed.subset`.

Primitive data vs derived API:
- primitive inputs: the ambient set `C`, the intermediate set `D`, and the face `C'`;
- derived outputs: the face or exposed-face status of `C'` inside `D`.

The source assumes `D` is convex because it is phrased with the textbook face definition. For
clause (1), the source-facing owner `Set.IsFace` only needs `C' ⊆ D ⊆ C`, so that convexity
hypothesis is redundant. Clause (2) is monotonicity of `IsExposed` under intermediate ambient
sets and likewise does not need convexity of `D`.
-/

open scoped Rockafellar

/- Text 18.0.13 (1): if `C'` is a face of `C` and `C' ⊆ D ⊆ C`, then `C'` is also a face of `D`.
This is exactly the owner theorem `Set.IsFace.mono`; the source convexity hypothesis on `D` is
redundant here. -/
recall Set.IsFace.mono

/- Text 18.0.13 (1), notation form: the same monotonicity at the chapter face-family surface
`𝓕[R](·)`, on the canonical owner-namespace bridge theorem. -/
recall Set.IsFace.mem_faces_mono

/- Text 18.0.13 (2): if `C'` is exposed in `C` and `C' ⊆ D ⊆ C`, then `C'` is also exposed in
`D`. This is exactly the canonical owner theorem `IsExposed.mono`; the source
convexity assumption on `D` is redundant in this owner formulation. -/
recall IsExposed.mono
