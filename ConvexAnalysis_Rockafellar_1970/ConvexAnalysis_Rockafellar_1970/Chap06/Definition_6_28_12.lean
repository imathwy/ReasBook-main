import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

noncomputable section

universe u v w

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.12 writes the Fenchel conjugate by its pointwise supremum
  formula and, in the chapter codomain layer, by the equivalent negative-infimum formula.
- `core/canonical`: these are already owned by `convexConjugate` and its canonical bridge theorem
  family from `Chap03.Defn_12_2`, at the primitive pairing and codomain abstraction layers.
- `bridge/view`: this file is a recap/reuse surface only; it should reuse those owners directly
  instead of adding alias theorem names.

Abstraction checks:
- no over-concrete `ℝ`/`EReal` lock-in is needed;
- the generic codomain layer remains `SupSet` + subtraction + pairing;
- the chapter-specific codomain bridge remains the existing `WithTopBot α` theorem;
- no extra wrapper owner/API is introduced.
-/

/- Definition 6.28.12: the Fenchel conjugate owner is exactly the existing canonical declaration. -/
recall convexConjugate

/- Canonical source-facing supremum formula for `f⋆`. -/
recall convexConjugate_eq_iSup_pairing_sub

/- Chapter-facing `WithTopBot α` bridge to the equivalent negative-infimum formula. -/
recall convexConjugate_eq_neg_iInf_sub_pairing
