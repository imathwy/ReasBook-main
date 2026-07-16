import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap21.Lemma_21_33_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.31.6:
- primary domain: braided monoidal commutativity for the relative derived cup product on
  `D(𝒪_X)` and `D(𝒪_Y)`;
- sampled owner declarations:
  `CategoryTheory.relativeDerivedCupProduct`,
  `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`,
  `CategoryTheory.BraidedCategory` via `β_`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the cup product is owned by
  `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`, specialized to the canonical
  ambient tensor `curriedTensor` on the derived categories of module sheaves on ringed spaces, so
  this file should reuse that owner directly rather than rebuilding a second ringed-space theorem
  with the same interface; the commutativity constraint is therefore the braided owner morphism
  `β_`, not an arbitrary chosen swap isomorphism;
- primitive data: the adjunction `Lf^* ⊣ Rf_*`, the pullback-tensor comparison
  `Lf^*(A ⊗ B) ≅ Lf^* A ⊗ Lf^* B`, and its braiding-compatibility square;
- derived API: the relative cup-product morphism and its `CommSq` compatibility with the source
  and target braidings.

Source/core/bridge triage:
- `source-facing`: the ringed-space commutativity square for relative cup products;
- `core/canonical`: `CategoryTheory.relativeDerivedCupProduct_commutative_commSq`;
- `bridge/view`: this file is recall-only, since the source-facing statement is exactly the
  categorical owner theorem specialized to derived categories of module sheaves on ringed spaces.
-/

/- Lemma 20.31.6 is exactly the categorical owner theorem
`CategoryTheory.relativeDerivedCupProduct_commutative_commSq`: for the ringed-space derived
pullback/pushforward adjunction `Lf^* ⊣ Rf_*`, the relative cup product of Remark 20.28.7 is
compatible with the braidings on source and target, provided the pullback-tensor comparison
intertwines those braidings. -/
recall CategoryTheory.relativeDerivedCupProduct_commutative_commSq

end AlgebraicGeometry.RingedSpace
