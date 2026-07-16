import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_43_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Lemma 7.43.3:
- primary domain: subtopoi of a sheaf topos arising from slice-topos inclusions at subterminal
  sheaves;
- sampled owner API:
  `IsSubterminal`,
  `IsSubterminal.mono_terminal_from`,
  `isSubterminal_of_mono_terminal_from`,
  `IsSubtopos`;
- best owner abstraction: the canonical left-hand owner is `IsSubterminal ℱ`, while
  `Mono (terminal.from ℱ)` is only the bridge/view expressing the same notion as a subobject of
  the terminal sheaf;
- primitive data: the sheaf `ℱ`;
- derived API: the source-facing reformulation in terms of `Mono (terminal.from ℱ)`.

Source/core/bridge triage:
- `source-facing`: the textbook phrasing that `ℱ ⟶ 1` is monic;
- `core/canonical`: `IsSubterminal ℱ` and `IsSubtopos J (Over.forget ℱ).essImage`;
- `bridge/view`: `Mono (terminal.from ℱ)` via the standard subterminal equivalence. -/
-- Proof sketch: for the forward implication, the slice localization `Sh(𝒞) / ℱ ⥤ Sh(𝒞)` is the
-- canonical open subtopos inclusion associated to the subterminal sheaf `ℱ`; for the reverse
-- implication, if this slice topos is presented by an embedding, then the localization counit is
-- an isomorphism, and the usual self-pullback/Yoneda argument shows that `ℱ ⟶ 1` is monic.
/-- Lemma 7.43.3: a sheaf `ℱ` on a site `(𝒞, J)` is subterminal if and only if the slice topos
`Sh(𝒞, J) / ℱ`, viewed in `Sh(𝒞, J)` through `Over.forget ℱ`, is a subtopos. -/
theorem sheaf_slice_isSubtopos_iff_isSubterminal
    (ℱ : Sheaf J (Type w)) :
    IsSubterminal ℱ ↔ IsSubtopos J (Over.forget ℱ).essImage := sorry

/-- Source-facing reformulation of Lemma 7.43.3: a sheaf `ℱ` is a subobject of the terminal sheaf
if and only if the slice topos `Sh(𝒞, J) / ℱ`, viewed in `Sh(𝒞, J)` through `Over.forget ℱ`, is a
subtopos. -/
theorem sheaf_slice_isSubtopos_iff_subterminal
    (ℱ : Sheaf J (Type w)) :
    Mono (terminal.from ℱ) ↔ IsSubtopos J (Over.forget ℱ).essImage := by
  constructor
  · intro hℱ
    letI : Mono (terminal.from ℱ) := hℱ
    exact (sheaf_slice_isSubtopos_iff_isSubterminal J ℱ).1
      isSubterminal_of_mono_terminal_from
  · intro hℱ
    exact (IsSubterminal.mono_terminal_from
      ((sheaf_slice_isSubtopos_iff_isSubterminal J ℱ).2 hℱ))

end

end CategoryTheory
