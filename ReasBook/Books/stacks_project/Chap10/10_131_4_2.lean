import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain triage:
* primary domain: functoriality of Kähler differentials for commutative-algebra squares;
* sampled owner API:
  `_root_.KaehlerDifferential.map`,
  `_root_.KaehlerDifferential.map_D`,
  `CommRingCat.KaehlerDifferential.map`,
  `CommRingCat.KaehlerDifferential.map_d`;
* source-facing layer: the textbook statement for a commutative square of commutative rings;
* core/canonical owner: `_root_.KaehlerDifferential.map`, the algebra-level map attached to a
  square of algebra maps;
* bridge/view: `CommRingCat.KaehlerDifferential.map` packages the same construction for a square in
  `CommRingCat`, and `CommRingCat.KaehlerDifferential.map_d` is its defining formula on universal
  differentials.

Primitive data are only the commutative square itself. The induced morphism on differentials and
its value on `d b` are derived API owned upstream, so this file should recall the categorical
bridge directly instead of keeping a parallel local presentation-level wrapper.
-/

/- 10.131.4.2: a commutative square of commutative rings induces the canonical morphism on Kähler
differentials. In the chapter ecosystem this source-facing statement is the `CommRingCat` bridge to
the owner construction `_root_.KaehlerDifferential.map`. -/
recall CommRingCat.KaehlerDifferential.map

/- On universal differentials, the canonical map sends `d b` to `d (φ(b))`. This is exactly the
companion lemma `CommRingCat.KaehlerDifferential.map_d`. -/
recall CommRingCat.KaehlerDifferential.map_d
