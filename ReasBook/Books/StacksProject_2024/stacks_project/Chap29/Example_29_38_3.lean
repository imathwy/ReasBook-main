import StacksProject_2024.Chap29.Lemma_29_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Source/core/bridge triage:
- `source-facing`: the Stacks item states a consequence of the source-facing owner
  `RelativelyAmple f L`;
- `bridge/view`: Chapter 29 already provides the existence-form theorem
  `isSeparated_of_exists_relativelyAmple`.

This file therefore keeps the source-facing owner theorem `RelativelyAmple.isSeparated` as a thin
bridge to that earlier chapter theorem, rather than duplicating a parallel proof route. -/

section

variable {X S : Scheme.{u}} {f : X ⟶ S} {L : X.Modules}

/-- Example 29.38.3: if an invertible `\mathcal O_X`-module `\mathcal L` is relatively ample over
`S`, then the structure morphism `f : X ⟶ S` is separated. -/
@[stacks 01VI]
theorem RelativelyAmple.isSeparated
    (hL : RelativelyAmple f L) : IsSeparated f := by
  exact isSeparated_of_exists_relativelyAmple f ⟨L, hL⟩

end

end AlgebraicGeometry
