import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import StacksProject_2024.Chap18.Definition_18_43_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory

namespace Sheaf

section Modules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]

/- Domain-style sampling for Lemma 18.43.6:
- primary domain: locally constant sheaves on a site and their behavior under the monoidal tensor on
  `Sheaf J (ModuleCat Λ)`;
- sampled owner declarations:
  `Sheaf.IsConstant`,
  `Sheaf.IsLocallyConstant`,
  `Sheaf.isLocallyConstant_of_isConstant`,
  `((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat Λ))).IsMonoidal`,
  `Sheaf.monoidalCategory`;
- best owner abstraction: the source-facing owner for local triviality is the earlier chapter
  declaration `Sheaf.IsLocallyConstant`; the tensor product is the canonical sheaf monoidal owner
  `Sheaf.monoidalCategory J (ModuleCat Λ)` induced from the site-level monoidal condition on
  `J.W`, not an arbitrary ambient monoidal structure on the sheaf category;
- primitive data: two sheaves `F`, `G` together with their `Sheaf.IsLocallyConstant` instances;
- derived API: the closure theorem asserting `Sheaf.IsLocallyConstant (F ⊗ G)`.

Source/core/bridge triage:
- `source-facing`: closure of locally constant sheaves of `Λ`-modules under tensor product;
- `core/canonical`: `Sheaf.IsLocallyConstant` from `Definition_18_43_1`;
- `bridge/view`: the canonical passage from the site-level monoidal hypothesis on `J.W` to the
  sheaf tensor via `Sheaf.monoidalCategory`.
-/

local instance : MonoidalCategory (Sheaf J (ModuleCat.{w} Λ)) :=
  Sheaf.monoidalCategory J (ModuleCat.{w} Λ)

-- Proof sketch: choose a common refinement of local trivializing covers for `F` and `G`. On each
-- member of that refinement the restricted sheaves are constant, and the tensor product of two
-- constant sheaves of `Λ`-modules is again constant with value the tensor product of the constant
-- module values.
/-- Lemma 18.43.6: the tensor product of two locally constant sheaves of `\Lambda`-modules on a
site is locally constant. -/
theorem isLocallyConstant_tensor
    {F G : Sheaf J (ModuleCat.{w} Λ)} [IsLocallyConstant F]
    [IsLocallyConstant G] :
    IsLocallyConstant (F ⊗ G) := sorry

end Modules

end Sheaf

end CategoryTheory
