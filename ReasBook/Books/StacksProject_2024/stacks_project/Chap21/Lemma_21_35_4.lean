import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.Tactic.Recall
import Mathlib.CategoryTheory.Triangulated.Adjunction
import StacksProject_2024.stacks_project.Chap21.RingedSiteDerivedBasic

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed
open scoped Pretriangulated.Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (RingedSiteDerived J 𝒪)]
variable [BraidedCategory (RingedSiteDerived J 𝒪)]
variable [MonoidalClosed (RingedSiteDerived J 𝒪)]
variable [HasShift (RingedSiteDerived J 𝒪) ℤ]
variable [∀ n : ℤ, (shiftFunctor (RingedSiteDerived J 𝒪) n).Additive]
variable [Pretriangulated (RingedSiteDerived J 𝒪)]

local notation "D" => RingedSiteDerived J 𝒪

/- Domain-style sampling for Lemma 21.35.4:
- primary domain: triangulated functors on derived categories, specialized to derived internal Hom
  on `D(𝒪)`;
- sampled owner declarations:
  `RingedSiteDerived`,
  `CategoryTheory.ihom`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`,
  `Functor.isTriangulated_of_op`;
- best owner abstraction: this item is a specialization/recall file. Once `D(𝒪)` is
  equipped with its braided closed monoidal pretriangulated structure, mathlib already owns the
  exactness of the target-variable internal-Hom functor `ihom K` and of the source-variable owner
  `((MonoidalClosed.internalHom).flip.obj L : Dᵒᵖ ⥤ D)`;
- primitive data: only the ambient braided closed monoidal triangulated structure on `D(𝒪)`;
- derived API: exactness of the derived internal-Hom functors `RHom(K, -)` and `RHom(-, L)`.

Source/core/bridge triage:
- `source-facing`: Lemma 21.35.4, asserting exactness of derived internal Hom in each variable on
  `D(𝒪)`;
- `core/canonical`: the generic monoidal-closed exactness owners
  `Functor.CommShift₂.commShiftObj`,
  `Adjunction.isTriangulated_rightAdjoint`,
  `Functor.CommShift₂.commShiftFlipObj`, and
  `Functor.isTriangulated_of_op`;
- `bridge/view`: none beyond specializing those canonical owners to the ringed-site derived
  category `D = RingedSiteDerived J 𝒪`.

This numbered item is recall-only, but its main surface should still sit at the source-facing
ringed-site specialization: expose the exact specialized `CommShift` and `IsTriangulated`
statements for `ihom K` and `((MonoidalClosed.internalHom).flip.obj L : Dᵒᵖ ⥤ D)` as typed
recalls of the generic owner declarations, rather than as new theorem wrappers.
-/

variable (K L : D)

/- Lemma 21.35.4 (1), shift form: for fixed `K : D(𝒪)`, the derived internal-Hom functor
`RHom(K, -)`, namely `ihom K`, commutes with the triangulated shift on
`D = RingedSiteDerived J 𝒪`. -/
recall Functor.CommShift₂.commShiftObj :
  Functor.CommShift (ihom K) (1 : ℤ)

/- Lemma 21.35.4 (1), exactness form: for fixed `K : D(𝒪)`, the derived internal-Hom functor
`RHom(K, -)`, namely `ihom K`, is triangulated on
`D = RingedSiteDerived J 𝒪`. -/
recall Adjunction.isTriangulated_rightAdjoint :
  Functor.IsTriangulated (ihom K)

/- Lemma 21.35.4 (2), shift form: for fixed `L : D(𝒪)`, the source-variable derived internal-Hom
functor `RHom(-, L)`, written as
`((MonoidalClosed.internalHom).flip.obj L : Dᵒᵖ ⥤ D)`, commutes with the triangulated shift. -/
recall Functor.CommShift₂.commShiftFlipObj :
  Functor.CommShift (((MonoidalClosed.internalHom).flip.obj L : Dᵒᵖ ⥤ D)) (1 : ℤ)

/- Lemma 21.35.4 (2), exactness form: for fixed `L : D(𝒪)`, the source-variable derived
internal-Hom functor `RHom(-, L)`, written as
`((MonoidalClosed.internalHom).flip.obj L : Dᵒᵖ ⥤ D)`, is triangulated. -/
recall Functor.isTriangulated_of_op :
  Functor.IsTriangulated (((MonoidalClosed.internalHom).flip.obj L : Dᵒᵖ ⥤ D))

end

end SheafOfModules.RingedSite
