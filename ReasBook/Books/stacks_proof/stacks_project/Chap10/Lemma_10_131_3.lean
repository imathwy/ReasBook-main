import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
- primary domain: commutative-algebra derivations and the universal property of Kähler
  differentials;
- sampled owner declarations: `Derivation`, `KaehlerDifferential.D`,
  `Derivation.liftKaehlerDifferential`, `KaehlerDifferential.linearMapEquivDerivation`;
- best owner abstraction: `KaehlerDifferential.linearMapEquivDerivation`, with primitive owner data
  carried by `Derivation` and the universal derivation `KaehlerDifferential.D`;
- layer: `bridge/view`, since the source-facing statement identifies two canonical owner-side views
  of the same universal object;
- primitive data: an `R`-algebra `S`, an `S`-module `M`, and the universal derivation
  `KaehlerDifferential.D R S`;
- derived API: the induced equivalence between `S`-linear maps out of `Ω[S⁄R]` and
  `R`-derivations `S → M`.
-/

/- Lemma 10.131.3 is the canonical universal-property bridge for Kähler differentials: composing
with `KaehlerDifferential.D R S` identifies `S`-linear maps `Ω[S⁄R] →ₗ[S] M` with
`R`-derivations `S → M`, functorially in `M`. This is already owned upstream by
`KaehlerDifferential.linearMapEquivDerivation`, so the file should recall that owner theorem
directly rather than introduce a parallel local wrapper. -/
recall KaehlerDifferential.linearMapEquivDerivation
