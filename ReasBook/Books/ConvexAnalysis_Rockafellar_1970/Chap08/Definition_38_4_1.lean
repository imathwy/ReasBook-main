import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap08.Corollary_38_4_1

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Source/core/bridge triage for this item.

- `source-facing`: despite the legacy file name, this item is Rockafellar's Corollary 38.4.1 on
  the image `image F f`, asserting closedness, pointwise attainment of the defining infimum, and
  the adjoint-side conjugacy formula.
- `core/canonical`: the owner abstractions already live in the chapter as `Bifunction.image`,
  `Bifunction.adjoint`, `Bifunction.dom`, and the function-side closed/proper/convex owner
  `Function.IsClosedProperConvex`.
- `bridge/view`: this file contributes no new mathematics beyond the canonical Chapter 8
  formulation already present in `Items/Chap08/Corollary_38_4_1.lean`, so it should reuse that
  source-facing theorem family directly.

Primary mathematical domain:
- infimal images of convex bifunctions and their adjoint-side conjugacy/attainment properties.

Domain-style sampling used here:
- `Bifunction.image` from `Definition_38_0_4`;
- `Bifunction.adjoint` from `Lemma_31_0_8`;
- `Bifunction.dom` from `Theorem_38_1`;
- the canonical Corollary 38.4.1 theorem family in `Corollary_38_4_1`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → EReal` and a function `f : U → EReal`;
- primitive owner layer: the existing chapter owners `image F f` and `F⋆`, with the operational
  bifunction view `Function.swap (F⋆)` where needed;
- derived API: lower semicontinuity of `image F f`, pointwise attainment of the infimum defining
  `image F f`, and the conjugacy identity with `cl(image (Function.swap (F⋆)) (f⋆))`.

Layer target: `bridge/view`. This file now reuses the existing source-facing owner theorems
directly instead of maintaining a parallel local API.
-/

/- Corollary 38.4.1, closedness clause: the canonical owner theorem for closedness of `image F f`
under the common-relative-interior hypothesis is already
`lowerSemicontinuous_image_of_common_riDom`. -/
recall Bifunction.lowerSemicontinuous_image_of_common_riDom

/- Corollary 38.4.1, attainment clause: the canonical owner theorem for attainment of the defining
infimum of `image F f` is already
`exists_eq_image_of_common_riDom`. -/
recall Bifunction.exists_eq_image_of_common_riDom

/- Corollary 38.4.1, conjugacy clause: the canonical owner theorem is already
`Bifunction.convexConjugate_image_eq_cl_image_adjoint_conjugate_of_common_riDom`.
-/
recall
  Bifunction.convexConjugate_image_eq_cl_image_adjoint_conjugate_of_common_riDom
