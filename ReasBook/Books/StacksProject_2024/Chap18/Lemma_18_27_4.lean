import Mathlib
import StacksProject_2024.Chap18.Definition_18_23_1
import StacksProject_2024.Chap18.Lemma_18_19_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open Opposite

noncomputable section

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma 18.27.4:
- primary domain: internal Hom in monoidal closed categories of presheaves and sheaves of modules
  over commutative ring objects;
- inspected owner declarations:
  `CategoryTheory.ihom`,
  `CategoryTheory.ihom.adjunction`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`;
- best owner abstraction:
  `ihom` for the target-variable internal Hom, and
  `((MonoidalClosed.internalHom).flip.obj 𝒢)` for the source-variable contravariant internal Hom;
- primitive data:
  a monoidal closed module category together with a fixed module object;
- derived API:
  preservation of limits by `ihom ℱ`, and preservation of limits by the contravariant
  source-variable owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the four Stacks clauses asserting that internal Hom preserves limits in the
  target variable and sends colimits in the source variable to limits;
- `core/canonical`: `ihom`, `ihom.adjunction`, `MonoidalClosed.internalHom`, and
  `MonoidalClosed.internalHomAdjunction₂`;
- `bridge/view`: the braided transport that identifies the source-variable internal Hom with the
  same owner after exchanging tensor factors.

The target-variable clauses are exact uses of the owner theorem
`Adjunction.rightAdjoint_preservesLimits`, so they should appear only as direct canonical use. The
source-variable clauses are organized around the actual contravariant internal-Hom owner
`((MonoidalClosed.internalHom).flip.obj 𝒢)`, not the opposite-valued bridge
`(((MonoidalClosed.internalHom).flip.obj 𝒢).rightOp)`.
-/

section Generic

variable {A : Type u} [Category.{v} A] [MonoidalCategory A] [BraidedCategory A]
variable [MonoidalClosed A]

-- Proof sketch: for fixed target `G`, the contravariant internal-Hom owner
-- `((MonoidalClosed.internalHom).flip.obj G)` is right adjoint to its `rightOp`, by currying in
-- one variable, transporting across the braiding, and currying back. Hence it preserves limits.
/-- For a fixed target object `G` in a braided monoidal closed category, the source-variable
contravariant internal-Hom functor preserves limits. -/
theorem internalHom_flip_obj_preservesLimits (G : A) :
    PreservesLimits ((MonoidalClosed.internalHom).flip.obj G) := by
  sorry

end Generic

section PresheafModulesTarget

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (ℱ : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Lemma 18.27.4 (1): for a presheaf of commutative rings `𝒪` and a fixed presheaf module `ℱ`,
the target-variable internal-Hom functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` commutes with arbitrary limits. This is
exactly the canonical right-adjoint preservation theorem applied to `ihom.adjunction ℱ`. -/
#check ((ihom.adjunction ℱ).rightAdjoint_preservesLimits : PreservesLimits (ihom ℱ))

end PresheafModulesTarget

section PresheafModulesSource

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v})
variable [MonoidalCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [BraidedCategory (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable [MonoidalClosed (PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))]
variable (𝒢 : PresheafOfModules (𝒪 ⋙ forget₂ CommRingCat RingCat))

/- Lemma 18.27.4 (2): for a fixed presheaf module `𝒢`, the source-variable contravariant
internal-Hom functor `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is the canonical owner
`((MonoidalClosed.internalHom).flip.obj 𝒢)`, and it preserves limits. Equivalently, it sends
colimits in presheaf modules to limits. -/
#check
  (internalHom_flip_obj_preservesLimits 𝒢 :
    PreservesLimits ((MonoidalClosed.internalHom).flip.obj 𝒢))

end PresheafModulesSource

section RingedSiteTarget

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (ℱ : _root_.ringedSiteModuleCategory J 𝒪)

/- Lemma 18.27.4 (3): on a ringed site `(C, J, 𝒪)`, for a fixed sheaf module `ℱ`, the
target-variable internal-Hom functor `𝒢 ↦ ℋom_𝒪(ℱ, 𝒢)` commutes with arbitrary limits. This is
again the direct owner theorem `rightAdjoint_preservesLimits` specialized to `ihom.adjunction ℱ`.
-/
#check ((ihom.adjunction ℱ).rightAdjoint_preservesLimits : PreservesLimits (ihom ℱ))

end RingedSiteTarget

section RingedSiteSource

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [MonoidalCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [BraidedCategory (_root_.ringedSiteModuleCategory J 𝒪)]
variable [MonoidalClosed (_root_.ringedSiteModuleCategory J 𝒪)]
variable (𝒢 : _root_.ringedSiteModuleCategory J 𝒪)

/- Lemma 18.27.4 (4): for a fixed sheaf module `𝒢`, the source-variable contravariant internal-Hom
functor `ℱ ↦ ℋom_𝒪(ℱ, 𝒢)` is the canonical owner `((MonoidalClosed.internalHom).flip.obj 𝒢)`, and
it preserves limits. Equivalently, it sends colimits in sheaves of modules to limits. -/
#check
  (internalHom_flip_obj_preservesLimits 𝒢 :
    PreservesLimits ((MonoidalClosed.internalHom).flip.obj 𝒢))

end RingedSiteSource

end CategoryTheory
