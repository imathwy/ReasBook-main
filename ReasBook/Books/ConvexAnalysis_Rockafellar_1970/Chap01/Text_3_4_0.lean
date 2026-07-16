import Mathlib.Data.Set.Operations
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.4.0 introduces the image `AC` and inverse image `A⁻¹D` of subsets under
  a map (in the source text, a linear transformation).
- `core/canonical`: the owner abstraction is the ordinary function-level set API `Set.image` and
  `Set.preimage`; a linear map is used only through its coercion to a function.
- `bridge/view`: the textbook formulas `AC = {Ax | x ∈ C}` and `A⁻¹D = {x | Ax ∈ D}` are exactly
  the standard notations `A '' C` and `A ⁻¹' D`, together with the canonical membership bridge
  theorems `Set.mem_image` and `Set.mem_preimage`.
- Primitive data vs derived API: the map `A` and the sets `C` and `D` are primitive; image and
  inverse image are direct canonical set constructions.
- Domain-style sampling: the sampled owner declarations are `Set.image`, `Set.preimage`,
  `Set.mem_image`, and `Set.mem_preimage` from `Mathlib.Data.Set.Operations`. On the project side,
  `Text_1_2`, `Text_3_1_4`, and `Text_3_1_6` show the same exact-recall owner-reuse pattern,
  while `Theorem_3_4` and `Text_3_4_2` consume this file through the same canonical set
  image/preimage notation.
- Layer target: `core/canonical`; the source text is only recalling the standard image/preimage
  constructions, so the main public entries remain direct `recall`s of the owner declarations and
  their atomic membership bridges.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the codomain fully generic (`α → β`), since only set image/preimage
  is used.
- Scalar/ambient-structure check: no scalar/topological/linear structure is mathematically
  primitive in this item, so none is exposed.
- Owner check: keep canonical `Set.image` and `Set.preimage`; linear maps are downstream
  specializations via coercions to functions.
- Topology check: this item is not topology-facing, so no intrinsic/relative topology refactor is
  applicable.
- Owner-name and notation check: use short canonical owners and textbook-primary notation
  (`f '' C`, `f ⁻¹' D`) directly on the owner theorems.
-/

/- Text 3.4.0: for a map `f` (hence in particular for linear transformations via coercion),
the textbook formulas `f(C) = {f x | x ∈ C}` and `f⁻¹(D) = {x | f x ∈ D}` are the canonical set
image and preimage constructions, written `f '' C` and `f ⁻¹' D`; the owner declarations are
`Set.image` and `Set.preimage`. -/
recall Set.image

/- The inverse-image notation `f⁻¹(D) = {x | f x ∈ D}` is the canonical set preimage
`Set.preimage`, written `f ⁻¹' D`. -/
recall Set.preimage

/- The textbook set-builder description `{f x | x ∈ C}` is the canonical membership bridge theorem
`Set.mem_image`. -/
recall Set.mem_image

/- The textbook set-builder description `{x | f x ∈ D}` is the canonical membership bridge theorem
`Set.mem_preimage`. -/
recall Set.mem_preimage
