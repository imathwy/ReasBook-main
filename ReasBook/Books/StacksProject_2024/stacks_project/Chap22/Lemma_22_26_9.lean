import Mathlib.CategoryTheory.Localization.Predicate
import StacksProject_2024.Chap22.Definition_22_3_2
import StacksProject_2024.Chap22.Example_22_26_8_Differential_graded_category_of_differential_graded_modules

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MorphismProperty
open DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "DGA" => CochainDGAlgebra R
local notation "Mod_(" A ")" => @DifferentialGradedModule R _ A
local notation:25 A " ⟶dga " B => @CochainDGAlgebra.Hom R _ A B

-- Source/core/bridge triage:
-- * source-facing: restriction of scalars for differential graded modules along
--   `φ : A ⟶dga E`;
-- * core/canonical: the Chapter 22 owners `DifferentialGradedModule`,
--   `DifferentialGradedCategory.DgFunctor`, and the induced homotopy-category bridge
--   `DgFunctor.mapK`;
-- * bridge/view: the underlying ordinary functor on differential graded modules and the
--   canonical homotopy-category functor `(φ.restrictDgFunctor).mapK`.
--
-- Semantic recall note: the canonical Chapter 22 owners here are `CochainDGAlgebra.Hom`,
-- `DifferentialGradedModule`, `dgModulesDifferentialGradedCategory`, and `DgFunctor.mapK`.
-- The restriction-of-scalars construction is therefore stated directly on those owners.

namespace CochainDGAlgebra.Hom

variable {A E : DGA}

/-- Restriction of scalars of a differential graded `E`-module along `φ : A ⟶ E`. -/
def restrictModule
    (φ : A ⟶dga E) (M : Mod_(E)) :
    Mod_(A) where
  X := M.X
  d := M.d
  smul n m :=
    { toFun := fun x ↦
        { toFun := fun a ↦ M.smul n m x (φ m a)
          map_add' := by
            sorry
          map_smul' := by
            sorry }
      map_add' := by
        sorry
      map_smul' := by
        sorry }
  d_sq := M.d_sq
  smul_one := by
    sorry
  smul_mul := by
    sorry
  comm_d := by
    sorry

/-- The restriction of scalars keeps the same underlying graded `R`-module. -/
@[simp] theorem restrictModule_X
    (φ : A ⟶dga E) (M : Mod_(E)) (n : ℤ) :
    (φ.restrictModule M).X n = M.X n :=
  rfl

/-- Restriction of scalars on morphisms of differential graded modules. -/
private def restrictHom
    (φ : A ⟶dga E)
    {M N : Mod_(E)} (f : M ⟶ N) :
    φ.restrictModule M ⟶ φ.restrictModule N where
  hom := f.hom
  comm_d := f.comm_d
  comm_smul := by
    sorry

/-- Restriction of scalars on homogeneous morphisms between differential graded modules. -/
private def restrictGradedHom
    (φ : A ⟶dga E) {M N : Mod_(E)} {k : ℤ}
    (f : dgModuleGradedHom E M N k) :
    dgModuleGradedHom A (φ.restrictModule M) (φ.restrictModule N) k :=
  ⟨f.1, by
    sorry⟩

/-- The ordinary restriction functor on categories of differential graded modules induced by
`φ : A ⟶ E`. -/
def restrictFunctor
    (φ : A ⟶dga E) :
    Mod_(E) ⥤ Mod_(A) where
  obj M := φ.restrictModule M
  map f := restrictHom φ f
  map_id := by
    intro M
    rfl
  map_comp := by
    intro M N P f g
    rfl

/-- The restriction functor acts on objects by the explicit restricted differential graded
module. -/
@[simp] theorem restrictFunctor_obj
    (φ : A ⟶dga E) (M : Mod_(E)) :
    (φ.restrictFunctor.obj M) = φ.restrictModule M :=
  rfl

/-- Lemma 22.26.9: a homomorphism `φ : (A, d) ⟶ (E, d)` induces the restriction-of-scalars
functor of differential graded categories
`Mod^{dg}_{(E, d)} ⥤ Mod^{dg}_{(A, d)}` from Example `22.26.8`. -/
@[stacks 09LD]
def restrictDgFunctor
    (φ : A ⟶dga E) :
    DgFunctor R (Mod_(E)) (Mod_(A)) where
  obj M := φ.restrictModule M
  map f := restrictGradedHom φ f
  map_add := by
    sorry
  map_smul := by
    sorry
  map_d := by
    sorry
  map_id := by
    sorry
  map_comp := by
    sorry

/-- The restriction DG functor acts on objects by the explicit restricted differential graded
module. -/
@[simp] theorem restrictDgFunctor_obj
    (φ : A ⟶dga E) (M : Mod_(E)) :
    (φ.restrictDgFunctor.obj M) = φ.restrictModule M :=
  rfl

/-- Passing to homotopy categories after restriction of scalars is the canonical specialization
of `DifferentialGradedCategory.DgFunctor.mapK`. -/
@[simp] theorem restrictDgFunctor_mapK_obj
    (φ : A ⟶dga E) (M : K R (Mod_(E))) :
    ((φ.restrictDgFunctor).mapK.obj M).obj = φ.restrictModule M.obj :=
  rfl

/-- The localized restriction-of-scalars functor on derived categories induced by
`φ : A ⟶ E`. This is the canonical `Localization.lift` of `φ.restrictDgFunctor`. -/
abbrev restrictionDerived
    (φ : A ⟶dga E)
    (QisA : MorphismProperty (K R (Mod_(A))))
    (QisE : MorphismProperty (K R (Mod_(E))))
    (hRestriction_inverts : QisE.IsInvertedBy (((φ.restrictDgFunctor).mapK) ⋙ QisA.Q)) :
    QisE.Localization ⥤ QisA.Localization :=
  (Localization.lift (((φ.restrictDgFunctor).mapK) ⋙ QisA.Q) hRestriction_inverts QisE.Q :
    QisE.Localization ⥤ QisA.Localization)

end CochainDGAlgebra.Hom

end
