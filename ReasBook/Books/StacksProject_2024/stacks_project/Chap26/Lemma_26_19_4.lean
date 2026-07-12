import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the exact canonical owner
-- `AlgebraicGeometry.quasiCompact_comp` for composition-stability of quasi-compact scheme
-- morphisms. Nearby Chapter 26 files `Lemma_26_19_3` and `Lemma_26_19_5` use the same
-- recall-only pattern for pure owner-level facts.
/-
Lemma 26.19.4: The composition of quasi-compact morphisms is quasi-compact. This is a pure
canonical recall of mathlib's instance `AlgebraicGeometry.quasiCompact_comp`.
-/
recall AlgebraicGeometry.quasiCompact_comp
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiCompact g] :
    QuasiCompact (f ≫ g)
