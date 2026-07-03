import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

scoped[DerivedExt] notation:max "Ext^" n "(" X ", " Y ")" =>
  CategoryTheory.ShiftedHom X Y n

end CategoryTheory

open CategoryTheory
open CategoryTheory.Abelian
open scoped DerivedExt

universe w' w v u

/- Domain-style sampling for Ext groups:
- primary domain: shifted morphism groups in derived categories and their specialization to
  objects of an abelian category;
- sampled owner declarations:
  `ShiftedHom`,
  `ShiftedHom.homEquiv`,
  `Ext`,
  `Ext.homEquiv`;
- best owner abstraction: for `X Y : D(𝒜)` the source-facing surface is `Ext^i(X, Y)`, whose core
  owner is `ShiftedHom X Y i`; for `A B : 𝒜` the canonical object-level bridge is `Ext A B n`,
  together with `Ext.homEquiv`;
- primitive data: a pair of objects in the derived category and a shift degree;
- derived API: the specialization to objects of `𝒜` via the degree-zero single-complex
  embedding.

Source/core/bridge triage:
- `source-facing`: the Stacks definition `Ext^i_𝒜(X, Y)`, written as `Ext^i(X, Y)`
- `core/canonical`: `ShiftedHom X Y i`
- `bridge/view`: `Ext` and `Ext.homEquiv`

No new alias or wrapper is needed here: `Ext^i(X, Y)` is only notation for the canonical owner
`ShiftedHom X Y i`, and the chapter-level `Ext` on objects of `𝒜` is already owned by `Ext`.
-/

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜]
variable (X Y : DerivedCategory 𝒜) (i : ℤ)

/- Definition 13.27.1: for objects `X Y : D(𝒜)`, the `i`-th extension group is written
`Ext^i(X, Y)`; this is exactly the canonical owner `ShiftedHom X Y i`, so by definition it is
`X ⟶ Y⟦i⟧`, and via the shift equivalence it may equally be read as morphisms `X[-i] ⟶ Y`. -/
#check Ext^i(X, Y)

/- Underlying core owner. -/
recall ShiftedHom

end

section

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w'} 𝒜] [HasExt.{w} 𝒜]
variable (A B : 𝒜) (n : ℕ)

/- For objects of the abelian category itself, the canonical owner is
`Ext`, which is already the specialization of derived `Ext^(n : ℤ)(-, -)` to the
single complexes `A[0]` and `B[0]`. -/
recall Ext

/- Companion bridge: `Ext.homEquiv` is the exact owner theorem identifying
`Ext A B n` with the derived extension group
`Ext^(n : ℤ)(((singleFunctor 𝒜 0).obj A), ((singleFunctor 𝒜 0).obj B))`. -/
recall Ext.homEquiv

end
