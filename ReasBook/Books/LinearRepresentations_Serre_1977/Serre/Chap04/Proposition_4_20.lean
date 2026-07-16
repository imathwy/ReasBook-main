import Mathlib.Tactic.Recall
import LinearRepresentations_Serre_1977.Serre.Chap02.Proposition_2_2_1_3

/- Source/core/bridge triage:
- `source-facing`: Proposition 4-20 records the symmetric/alternating-square character formulas
  and the tensor-square decomposition used later in Chapter 4's compact continuous setting.
- `core/canonical`: `Representation.char_symmetricSquare`,
  `Representation.char_alternatingSquare`,
  `Representation.char_symmetricSquare_add_char_alternatingSquare`, and
  `Representation.symmetricAlternatingSquareEquivTensor`.
- `bridge/view`: the source-facing direction of the decomposition is the inverse equivalence
  `ρ.symmetricAlternatingSquareEquivTensor.symm`.

The Chapter 4 continuity and compactness hypotheses do not change these owners. This item is
therefore recall-only: separate `_of_isContinuousCompact` wrappers would duplicate the earlier
canonical API without improving repository reuse.
-/

/- Proposition 4-20 (1): the character of `Sym² ρ` is
`(1 / 2) * (ρ.character s ^ 2 + ρ.character (s ^ 2))`. In Chapter 4 this is applied to
finite-dimensional continuous complex representations of compact groups, but the formula itself is
already the canonical theorem `Representation.char_symmetricSquare`. -/
recall Representation.char_symmetricSquare

/- Proposition 4-20 (2): the character of `Alt² ρ` is
`(1 / 2) * (ρ.character s ^ 2 - ρ.character (s ^ 2))`. In Chapter 4 this is applied to
finite-dimensional continuous complex representations of compact groups, but the formula itself is
already the canonical theorem `Representation.char_alternatingSquare`. -/
recall Representation.char_alternatingSquare

/- Proposition 4-20 (3): the symmetric- and alternating-square characters add to `ρ.character^2`.
In Chapter 4 this is applied in the compact continuous setting, but the identity itself is already
the canonical theorem `Representation.char_symmetricSquare_add_char_alternatingSquare`. -/
recall Representation.char_symmetricSquare_add_char_alternatingSquare

namespace Representation

section

universe u v w

variable {k : Type u} [CommRing k] [Invertible (2 : k)]
variable {G : Type v} [Monoid G]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable (ρ : Representation k G V)

/- Proposition 4-20 (4): the tensor square is equivariantly isomorphic to the direct product of
the symmetric and alternating squares. The canonical owner is
`ρ.symmetricAlternatingSquareEquivTensor : ((Sym² ρ).prod (Alt² ρ)).Equiv (ρ.tprod ρ)`, and the
source-facing direction is its inverse. -/
#check ρ.symmetricAlternatingSquareEquivTensor.symm

end

end Representation
