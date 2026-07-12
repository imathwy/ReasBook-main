import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

section

variable {V : Type u} [Category.{v} V] [Preadditive V]
variable {M N : CochainComplex V ℤ}
variable (f g : M ⟶ N)

-- Semantic search note: `lean_leansearch` was unavailable in this runner; the owner/API choice
-- was verified against the local analogue `Definition_22_5_1`.

/- Domain-style sampling for Definition 24.21.1:
- primary domain: homotopies of cochain-complex morphisms in a preadditive category;
- sampled canonical declarations:
  `Homotopy`,
  `homotopic`,
  `Homotopy.compLeft`,
  `Homotopy.compRight`;
- best owner abstraction: the owner is the canonical chain-homotopy structure `Homotopy f g` on
  `CochainComplex V ℤ`;
- primitive data: the degree-`(-1)` homotopy components together with the chain-homotopy identity
  encoded by the owner fields;
- bridge/view: the corresponding relation `homotopic V (up ℤ) f g`, i.e. existence of such a
  homotopy.

In Chapter 24, this owner is applied to the preadditive category of differential graded
`\mathcal A`-modules on a ringed site. The `\mathcal A`-linearity is ambient in that category, so
no separate chapter-local wrapper is needed.
-/

/- Definition 24.21.1: a homotopy between morphisms of differential graded modules is the
canonical owner `Homotopy`; the proposition that two morphisms are homotopic is the associated
relation `homotopic`. On cochain complexes, this is exactly the standard degree-`(-1)` chain
homotopy notion. -/
#check (Homotopy f g)
#check (homotopic V (up ℤ) f g)

end

end CategoryTheory
