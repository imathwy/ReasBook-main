import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Triangulated.Adjunction
import StacksProject_2024.Chap20.«20_42_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed
open scoped Pretriangulated.Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [Limits.HasZeroObject (RingedSpaceDerived X)]
variable [Preadditive (RingedSpaceDerived X)]
variable [HasShift (RingedSpaceDerived X) ℤ]
variable [∀ n : ℤ, (shiftFunctor (RingedSpaceDerived X) n).Additive]
variable [Pretriangulated (RingedSpaceDerived X)]
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

local notation "DMod" => RingedSpaceDerived X

/- Domain-style sampling for Lemma 20.42.4:
- primary domain: triangulated functors on derived categories, specialized to derived internal Hom
  on `D(𝒪_X)`;
- sampled owner declarations:
  `RingedSpaceDerived`,
  `CategoryTheory.ihom`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`,
  `Functor.isTriangulated_of_op`;
- best owner abstraction: this item is a specialization/recall file. Once `D(𝒪_X)` is equipped
  with its braided closed monoidal pretriangulated structure, mathlib already owns the exactness
  of the target-variable internal-Hom functor `ihom K` and of the source-variable owner
  `((MonoidalClosed.internalHom).flip.obj L : DModᵒᵖ ⥤ DMod)`;
- primitive data: only the ambient braided closed monoidal triangulated structure on `D(𝒪_X)`;
- derived API: exactness of `RHom(K, -)` and `RHom(-, L)`.

Source/core/bridge triage:
- `source-facing`: Lemma 20.42.4, asserting exactness of derived internal Hom in each variable on
  `D(𝒪_X)`;
- `core/canonical`: the generic monoidal-closed exactness owners
  `Functor.CommShift₂.commShiftObj`,
  `Adjunction.isTriangulated_rightAdjoint`,
  `Functor.CommShift₂.commShiftFlipObj`, and
  `Functor.isTriangulated_of_op`;
- `bridge/view`: none beyond specializing those canonical owners to the ringed-space derived
  category `DMod = RingedSpaceDerived X`.

This numbered item is recall-only, but its main surface should still sit at the source-facing
ringed-space specialization: expose the exact specialized `CommShift` and `IsTriangulated`
statements for `ihom K` and `((MonoidalClosed.internalHom).flip.obj L : DModᵒᵖ ⥤ DMod)` as typed
recalls of the generic owner declarations, rather than as metaprogramming probes or new theorem
wrappers.
-/

variable (K : DMod)

/- Lemma 20.42.4 (1), shift form: for fixed `K : D(𝒪_X)`, the derived internal-Hom functor
`RHom(K, -)`, namely `ihom K`, commutes with the triangulated shift on
`DMod = RingedSpaceDerived X`. -/
recall Functor.CommShift₂.commShiftObj :
  Functor.CommShift (ihom K) (1 : ℤ)

/- Lemma 20.42.4 (1), exactness form: for fixed `K : D(𝒪_X)`, the derived internal-Hom functor
`RHom(K, -)`, namely `ihom K`, is triangulated on `DMod = RingedSpaceDerived X`. -/
recall Adjunction.isTriangulated_rightAdjoint :
  Functor.IsTriangulated (ihom K)

variable (L : DMod)

/- Lemma 20.42.4 (2), shift form: for fixed `L : D(𝒪_X)`, the source-variable derived
internal-Hom functor `RHom(-, L)`, written as
`((MonoidalClosed.internalHom).flip.obj L : DModᵒᵖ ⥤ DMod)`, commutes with the triangulated
shift. -/
recall Functor.CommShift₂.commShiftFlipObj :
  Functor.CommShift (((MonoidalClosed.internalHom).flip.obj L : DModᵒᵖ ⥤ DMod)) (1 : ℤ)

/- Lemma 20.42.4 (2), exactness form: for fixed `L : D(𝒪_X)`, the source-variable derived
internal-Hom functor `RHom(-, L)`, written as
`((MonoidalClosed.internalHom).flip.obj L : DModᵒᵖ ⥤ DMod)`, is triangulated. -/
recall Functor.isTriangulated_of_op :
  Functor.IsTriangulated (((MonoidalClosed.internalHom).flip.obj L : DModᵒᵖ ⥤ DMod))

end

end AlgebraicGeometry.RingedSpace
