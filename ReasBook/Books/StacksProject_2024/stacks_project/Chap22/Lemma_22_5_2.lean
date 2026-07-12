import Mathlib.Tactic.Recall
import StacksProject_2024.Chap12.Lemma_12_13_7

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: the textbook operation sending a homotopy between `f` and `g` to the induced
  homotopy between `c ∘ f ∘ a` and `c ∘ g ∘ a`;
- `core/canonical`: `Homotopy` on cochain complexes;
- `bridge/view`: the Chapter 12 cochain-side whiskering construction
  `Homotopy.cochainWhisker` together with its degreewise formula
  `Homotopy.cochainWhisker_hom`.

This file is therefore a direct recall of the existing Chapter 12 bridge, not a second owner or a
new compatibility wrapper in Chapter 22.
-/

/-
Lemma 22.5.2: after identifying differential graded `A`-modules with the Chapter 22 cochain
complex model, the source statement is exactly the whiskering construction
`Homotopy.cochainWhisker`. It sends a homotopy `h : Homotopy f g` to the homotopy between
`c ∘ f ∘ a` and `c ∘ g ∘ a`, written in Lean as `((a ≫ f) ≫ c)` and `((a ≫ g) ≫ c)`.
-/
recall Homotopy.cochainWhisker

/- Companion recall: the degreewise component of this whiskered homotopy is the source formula
`c^{i - 1} ∘ h^i ∘ a^i`, recorded canonically by `Homotopy.cochainWhisker_hom`. -/
recall Homotopy.cochainWhisker_hom
