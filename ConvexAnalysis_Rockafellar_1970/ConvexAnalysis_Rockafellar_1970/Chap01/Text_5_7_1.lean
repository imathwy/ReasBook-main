import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.7.1 names the function `Ah` from Theorem 5.7 as the image of `h`
  under `A`, and names `gA` as the inverse image of `g` under `A`.
- `core/canonical`: the chapter owner declaration for `Ah` is `Function.linearImage`; the
  inverse-image operation on functions is ordinary precomposition, written on theorem surfaces as
  `g ∘ A`.
- `bridge/view`: the only bridge needed is the direct identification of the textbook notation
  `gA` with ordinary precomposition (`(g ∘ A) x = g (A x)` via `Function.comp_apply`), together
  with the source-facing defining formula `Function.linearImage_eq_sInf_image` for `Ah`.
- Primitive data vs derived API: the primitive objects are `A`, `g`, and `h`; this item should
  reuse the existing chapter declaration and ordinary function composition rather than introduce
  a parallel alias.
- Domain-style sampling used here: `Function.linearImage`, `Function.linearImage_eq_sInf_image`,
  and `Function.comp_apply`.
- Ambient minimization: these declarations already live at the codomain-generic
  `InfSet` layer for `Ah` and the plain function-composition layer for `gA`,
  so this recall item should not reintroduce Euclidean coordinates, dimension parameters, or an
  `ℝ`-specific presentation.
- Abstraction checks:
  - codomain/ambient layer: `Ah` is already at the intrinsic `InfSet` codomain layer, so no
    `EReal`/`ℝ` specialization is introduced here;
  - scalar/ambient structure: no scalar or module assumptions are needed for this recall item;
  - owner/model choice: keep the intrinsic chapter owner `Function.linearImage` and standard
    precomposition surface `g ∘ A`, not a coordinate or model-specific wrapper;
  - topology language: not applicable for this algebraic naming item;
  - owner naming / notation: use textbook-primary notation `g ∘ A` on the source-facing bridge,
    while reusing the canonical owner theorem `Function.comp_apply`.
- Layer target: `core/canonical` plus direct source bridge; this item should recall both owners
  and defining formulas on canonical theorem surfaces rather than keep a local theorem wrapper.
-/

/- Text 5.7.1: in Theorem 5.7, the function `Ah` is the chapter declaration
`Function.linearImage A h`, called the image of `h` under `A`. -/
recall Function.linearImage

/- Text 5.7.1 also records the defining formula
`Ah(y) = inf { h(x) | A x = y }`, exposed canonically by
`Function.linearImage_eq_sInf_image`. -/
recall Function.linearImage_eq_sInf_image

/- The defining pointwise formula for that inverse image is the canonical bridge
`Function.comp_apply : (g ∘ A) x = g (A x)`. -/
recall Function.comp_apply
