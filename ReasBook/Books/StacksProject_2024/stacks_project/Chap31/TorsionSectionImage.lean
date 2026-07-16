import StacksProject_2024.stacks_project.Chap06.Definition_6_27_1

-- Definitions for Lemma 31.11.1 and Definition 31.11.2.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]

/-- The image of `s` in the stalk `ℱ_x`. -/
def sectionImageAt
    (ℱ : X.Modules) {U : X.Opens} (s : ℱ.val.obj (op U))
    (x : U) : RingedSpace.stalkModuleCat ℱ x.1 :=
  TopCat.Presheaf.germ ℱ.val.presheaf U x.1 x.2 s

/-- The image of `s` in the stalk `ℱ_x` is torsion. -/
def sectionImageIsTorsionAt
    (ℱ : X.Modules) {U : X.Opens} (s : ℱ.val.obj (op U))
    (x : U) : Prop :=
  sectionImageAt ℱ s x ∈
    Submodule.torsion (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)

/-- The generic point of an integral scheme belongs to every nonempty open subset. -/
def genericPointInOpen
    (η : X) (hη : IsGenericPoint η (Set.univ : Set X))
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) : U :=
  ⟨η, (hη.mem_open_set_iff U.2).2 (by simpa [Set.inter_univ] using hU)⟩

/-- The image of `s` in the stalk at the generic point `η`. -/
def genericSectionImage
    (ℱ : X.Modules) (η : X) (hη : IsGenericPoint η (Set.univ : Set X))
    {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    RingedSpace.stalkModuleCat ℱ η :=
  sectionImageAt ℱ s (genericPointInOpen η hη hU)

/-- On a nonempty open of an integral scheme, the image of `s` in the canonical generic stalk. -/
def sectionImageAtGenericPoint
    (ℱ : X.Modules) {U : X.Opens} (hU : Set.Nonempty (U : Set X)) (s : ℱ.val.obj (op U)) :
    RingedSpace.stalkModuleCat ℱ (genericPoint X) :=
  genericSectionImage ℱ (genericPoint X) (genericPoint_spec X) hU s

end AlgebraicGeometry.Scheme.Modules
