import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.4 recalls the notion of a positively homogeneous function
  as a function-side owner.
- `core/canonical`: the owner abstraction is the generic chapter predicate
  `Function.PositivelyHomogeneous : (E → F) → Prop` from `Definition_4_8`, together with the
  intrinsic positive-scalar owner `Function.PositiveScalars` (notation `𝕜⁺`).
- `bridge/view`: the intrinsic positive-scalar view and the explicit pointwise scaling bridge are
  `Function.PositivelyHomogeneous.iff_forall_pos`,
  `Function.PositivelyHomogeneous.iff_forall_pos_scalar`,
  `Function.PositivelyHomogeneous.map_smul_pos`, and
  `Function.PositivelyHomogeneous.map_smul`.
- Primitive data vs derived API: the owner predicate is primitive; the intrinsic and textbook
  scalar-binder equivalences and the pointwise scaling theorems are the derived API.
- Domain-style sampling used here: `Function.PositivelyHomogeneous`,
  `Function.PositiveScalars`,
  `Function.PositivelyHomogeneous.iff_forall_pos`,
  `Function.PositivelyHomogeneous.iff_forall_pos_scalar`,
  `Function.PositivelyHomogeneous.map_smul_pos`, and
  `Function.PositivelyHomogeneous.map_smul`.
- Layer target: `core/canonical`; this file recalls the codomain-agnostic owner and its intrinsic
  bridge API rather than introducing a codomain-specialized wrapper surface.
-/

namespace Function

/- Text 5.4.4: the notion of a positively homogeneous function is the chapter owner
`PositivelyHomogeneous`. -/
recall PositivelyHomogeneous

/- Intrinsic owner for positive scalars used in positive-homogeneity surfaces. -/
recall PositiveScalars

/- Coercion bridge from the intrinsic positive-scalar action to ambient scalar action. -/
recall positiveScalars_smul_eq_coe_smul

/- Intrinsic positive-scalar view of the owner, using the positive subtype. -/
recall PositivelyHomogeneous.iff_forall_pos

/- Textbook scalar-plus-positivity binder form, as a bridge from the intrinsic owner. -/
recall PositivelyHomogeneous.iff_forall_pos_scalar

/- Pointwise scaling bridges for positive scalars, in subtype and textbook binder forms. -/
recall PositivelyHomogeneous.map_smul_pos
recall PositivelyHomogeneous.map_smul

end Function
