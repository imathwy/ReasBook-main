import Mathlib
import StacksProject_2024.Chap18.Lemma_18_41_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open SheafOfModules

noncomputable section

universe u

namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

private abbrev simplicialRing
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) (Δ : SimplexCategoryᵒᵖ) :
    Sheaf J RingCat.{u} :=
  ringSheaf J (A.obj Δ)

private abbrev simplicialRingMap
    (A : SimplicialObject (Sheaf J CommRingCat.{u}))
    {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ') :
    simplicialRing A Δ ⟶ simplicialRing A Δ' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map (A.map θ)

private noncomputable abbrev simplicialSheafModuleIdIso
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) (Δ : SimplexCategoryᵒᵖ) :
    SheafOfModules.restrictScalars (simplicialRingMap A (𝟙 Δ)) ≅
      𝟭 (SheafOfModules (simplicialRing A Δ)) :=
  SheafOfModules.pushforwardCongr
      (by
        simpa [simplicialRingMap] using
          congrArg ((sheafCompose J (forget₂ CommRingCat RingCat)).map) (A.map_id Δ)) ≪≫
    SheafOfModules.pushforwardId (simplicialRing A Δ)

private noncomputable abbrev simplicialSheafModuleCompIso
    (A : SimplicialObject (Sheaf J CommRingCat.{u}))
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) (η : Δ₂ ⟶ Δ₃) :
    SheafOfModules.restrictScalars (simplicialRingMap A η) ⋙
      SheafOfModules.restrictScalars (simplicialRingMap A θ) ≅
      SheafOfModules.restrictScalars (simplicialRingMap A (θ ≫ η)) :=
  SheafOfModules.pushforwardComp
      (φ := simplicialRingMap A θ) (ψ := simplicialRingMap A η) ≪≫
    SheafOfModules.pushforwardCongr
      (by
        simpa [simplicialRingMap] using
          congrArg ((sheafCompose J (forget₂ CommRingCat RingCat)).map) (A.map_comp θ η))

/-- Definition 21.41.1: for a site `\mathcal C` and a simplicial sheaf of rings
`\mathcal A_\bullet`, a simplicial `\mathcal A_\bullet`-module is a family of sheaves of
modules on `\mathcal C`, one in each simplicial degree, together with simplicial transition maps
that are linear over the corresponding structure-ring maps and satisfy the simplicial identities
through the canonical restriction-of-scalars comparison isomorphisms. This is the degreewise form
of a sheaf of modules over the sheaf of rings on `\Delta \times \mathcal C` associated to
`\mathcal A_\bullet`. -/
structure SimplicialSheafOfModules
    (A : SimplicialObject (Sheaf J CommRingCat.{u})) where
  /-- The sheaf of modules in a fixed simplicial degree. -/
  obj : ∀ Δ : SimplexCategoryᵒᵖ, SheafOfModules.{u} (simplicialRing A Δ)
  /-- The semilinear transition morphism attached to a simplicial operator. -/
  map : ∀ {Δ Δ' : SimplexCategoryᵒᵖ} (θ : Δ ⟶ Δ'),
    obj Δ ⟶ (SheafOfModules.restrictScalars (simplicialRingMap A θ)).obj (obj Δ')
  /-- The transition map attached to the identity simplicial operator is the identity. -/
  map_id : ∀ Δ : SimplexCategoryᵒᵖ,
    map (𝟙 Δ) = (simplicialSheafModuleIdIso A Δ).inv.app (obj Δ)
  /-- The transition map attached to a composite simplicial operator is the composite of the
  corresponding semilinear transition morphisms. -/
  map_comp : ∀ {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (θ : Δ₁ ⟶ Δ₂) (η : Δ₂ ⟶ Δ₃),
    map (θ ≫ η) =
      map θ ≫
        (SheafOfModules.restrictScalars (simplicialRingMap A θ)).map (map η) ≫
        (simplicialSheafModuleCompIso A θ η).hom.app (obj Δ₃)

namespace SimplicialSheafOfModules

variable {A : SimplicialObject (Sheaf J CommRingCat.{u})}

/-- A simplicial sheaf of modules can be evaluated at a simplicial degree to recover its sheaf of
modules in that degree. -/
instance : CoeFun (SimplicialSheafOfModules A) (fun _ ↦
    ∀ Δ : SimplexCategoryᵒᵖ, SheafOfModules.{u} (simplicialRing A Δ)) where
  coe M := M.obj

end SimplicialSheafOfModules

end CategoryTheory
