import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.39.4: compositions of flat ring homomorphisms are flat. -/
recall RingHom.Flat.comp

/- Companion recall: compositions of faithfully flat ring homomorphisms are faithfully flat.
Mathlib packages this as stability under composition of `RingHom.FaithfullyFlat`. -/
recall RingHom.FaithfullyFlat.stableUnderComposition

/- Companion recall: if `R → R'` is flat and `M'` is a flat `R'`-module, then `M'` is flat as an
`R`-module. -/
recall Module.Flat.trans

/- Companion recall: if `R → R'` is faithfully flat and `M'` is a faithfully flat `R'`-module,
then `M'` is faithfully flat as an `R`-module. -/
recall Module.FaithfullyFlat.trans
