import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the closed-immersion ideal-sheaf owner
-- `Scheme.Hom.ker` and the canonical closed-immersion API. For the source-facing annihilation
-- condition, the existing Chapter 17 closed-immersion API exposes the actual kernel ideal sheaf
-- as `RingedSpace.closedImmersionIdealSheaf i.toShHom`; local Chapter 30 precedent uses
-- `RingedSpace.Coh` for the coherent full subcategory.

/-- A module sheaf is annihilated by the ideal sheaf of a closed immersion when every local
section of that ideal acts by zero on every local section of the module. -/
def IsAnnihilatedByClosedImmersionIdeal {X Z : Scheme.{u}} (i : Z ⟶ X)
    (M : X.Modules) : Prop :=
  ∀ U : Opens X,
    ∀ s : (RingedSpace.closedImmersionIdealSheaf i.toShHom).val.obj (op U),
      ∀ m : M.val.obj (op U),
        ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
          (RingedSpace.Hom.toRingCatSheafHom i.toShHom))).val.app (op U) s) • m = 0

/-- The full-subcategory object property of coherent modules annihilated by the ideal sheaf of a
closed immersion. -/
def coherentAnnihilatedByClosedImmersionIdeal {X Z : Scheme.{u}} (i : Z ⟶ X) :
    ObjectProperty (RingedSpace.Coh X.toRingedSpace) :=
  fun M ↦ IsAnnihilatedByClosedImmersionIdeal i M.obj

/-- Unfold the sectionwise annihilation condition by the ideal sheaf of a closed immersion. -/
theorem isAnnihilatedByClosedImmersionIdeal_iff {X Z : Scheme.{u}} (i : Z ⟶ X)
    (M : X.Modules) :
    IsAnnihilatedByClosedImmersionIdeal i M ↔
      ∀ U : Opens X,
        ∀ s : (RingedSpace.closedImmersionIdealSheaf i.toShHom).val.obj (op U),
          ∀ m : M.val.obj (op U),
            ((kernel.ι (SheafOfModules.unitToPushforwardObjUnit
              (RingedSpace.Hom.toRingCatSheafHom i.toShHom))).val.app (op U) s) • m = 0 := sorry

/-- Pushforward along a closed immersion carries coherent modules to coherent modules. -/
theorem pushforward_obj_isCoherent_of_isClosedImmersion
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (G : RingedSpace.Coh Z.toRingedSpace) :
    (((SheafOfModules.isCoherent Z.toRingedSpace).ι ⋙ pushforward i).obj G).IsCoherent := sorry

/-- Pushforward along a closed immersion lands in the coherent modules annihilated by the kernel
ideal sheaf of the immersion. -/
theorem pushforward_mem_coherentAnnihilatedByKer
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (G : RingedSpace.Coh Z.toRingedSpace) :
    coherentAnnihilatedByClosedImmersionIdeal i
      ((ObjectProperty.lift (SheafOfModules.isCoherent X.toRingedSpace)
        ((SheafOfModules.isCoherent Z.toRingedSpace).ι ⋙ pushforward i)
        (pushforward_obj_isCoherent_of_isClosedImmersion i)).obj G) := sorry

/-- Lemma 30.9.8: for a closed immersion `i : Z ⟶ X` of locally Noetherian schemes, with
kernel ideal sheaf `\mathcal I = ker(\mathcal O_X ⟶ i_*\mathcal O_Z)` cutting out `Z`,
pushforward induces an equivalence from coherent `\mathcal O_Z`-modules to coherent
`\mathcal O_X`-modules annihilated by `\mathcal I`. -/
@[stacks 087T]
theorem closedImmersion_pushforward_coherentAnnihilatedByKer_isEquivalence
    {X Z : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsClosedImmersion i] :
    Functor.IsEquivalence
      (ObjectProperty.lift (coherentAnnihilatedByClosedImmersionIdeal i)
        (ObjectProperty.lift (SheafOfModules.isCoherent X.toRingedSpace)
          ((SheafOfModules.isCoherent Z.toRingedSpace).ι ⋙ pushforward i)
          (pushforward_obj_isCoherent_of_isClosedImmersion i))
        (pushforward_mem_coherentAnnihilatedByKer i)) := sorry

end AlgebraicGeometry.Scheme.Modules
