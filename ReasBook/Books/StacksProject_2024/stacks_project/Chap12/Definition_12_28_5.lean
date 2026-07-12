import Mathlib.Algebra.Homology.LeftResolution.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

universe v u

open CategoryTheory

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 12.28.5:
- primary domain: functorial choices of projective objects surjecting onto every object;
- sampled owner-style declarations:
  `ProjectivePresentation`,
  `EnoughProjectives`,
  `Abelian.LeftResolution (ObjectProperty.ι (isProjective C))`,
  `HasFunctorialInjectiveEmbeddings`;
- best owner abstraction: the source-facing owner is
  `HasFunctorialProjectiveSurjections C`, while
  `Abelian.LeftResolution (ObjectProperty.ι (isProjective C))` is the existing chosen-data
  canonical owner with the same primitive content reorganized through the full subcategory of
  projective objects;
- primitive data: a functor `P : C ⥤ Arrow C`, a proof `P ⋙ Arrow.rightFunc = 𝟭 C`, and the
  objectwise facts that each `P.obj A` is an epimorphism with projective source;
- derived API: the canonical objectwise bridge `presentation : ProjectivePresentation A`, the
  objectwise views `over`, `π`, and `overMap`, the source functor `overFunctor`, the canonical
  natural transformation `πNatTrans`, the bridge `toLeftResolution`, and the consequence
  `EnoughProjectives C`.

Source/core/bridge triage for Definition 12.28.5:
- source-facing: `HasFunctorialProjectiveSurjections C`;
- core/canonical: `Abelian.LeftResolution (ObjectProperty.ι (isProjective C))`;
- bridge/view: `toLeftResolution`, `Abelian.LeftResolution.hasFunctorialProjectiveSurjections`,
  and the induced `EnoughProjectives C`.

The projective presentation of each individual object is derived from the ambient owner, so it does
not need a parallel public wrapper API. -/

/-- Definition 12.28.5: a category has functorial projective surjections if it is equipped with a
functor `P : C ⥤ Arrow C` whose target functor is the identity, so that `P.obj A`
is a functorial choice of projective presentation of `A`. Concretely, each arrow `P.obj A` is an
epimorphism and each source `(P.obj A).left` is projective. -/
class HasFunctorialProjectiveSurjections (C : Type u) [Category.{v} C] where
  P : C ⥤ Arrow C
  rightFunc_comp_P : P ⋙ Arrow.rightFunc = 𝟭 C
  epi_obj (A : C) : Epi ((P.obj A).hom)
  projective_obj (A : C) : Projective ((P.obj A).left)

attribute [instance] HasFunctorialProjectiveSurjections.epi_obj
attribute [instance] HasFunctorialProjectiveSurjections.projective_obj

section HasFunctorialProjectiveSurjections

variable [HasFunctorialProjectiveSurjections C]

/-- The target of the chosen arrow `P.obj A` is canonically `A`. -/
@[simp]
private lemma HasFunctorialProjectiveSurjections.obj_right (A : C) :
    (HasFunctorialProjectiveSurjections.P.obj A).right = A := by
  simpa using Functor.congr_obj HasFunctorialProjectiveSurjections.rightFunc_comp_P A

/-- The canonical projective presentation determined by the chosen functorial surjection onto
`A`. -/
def HasFunctorialProjectiveSurjections.presentation (A : C) : ProjectivePresentation A where
  p := (HasFunctorialProjectiveSurjections.P.obj A).left
  projective := HasFunctorialProjectiveSurjections.projective_obj A
  f := (HasFunctorialProjectiveSurjections.P.obj A).hom ≫
    eqToHom (HasFunctorialProjectiveSurjections.obj_right A)
  epi := by infer_instance

/-- The chosen projective object over `A`. -/
abbrev HasFunctorialProjectiveSurjections.over (A : C) : C :=
  (HasFunctorialProjectiveSurjections.P.obj A).left

/-- The chosen functorial projective surjection onto `A`. -/
abbrev HasFunctorialProjectiveSurjections.π (A : C) :
    HasFunctorialProjectiveSurjections.over A ⟶ A :=
  (HasFunctorialProjectiveSurjections.P.obj A).hom ≫
    eqToHom (HasFunctorialProjectiveSurjections.obj_right A)

/-- The map between chosen projective sources induced by a morphism. -/
abbrev HasFunctorialProjectiveSurjections.overMap {A B : C} (f : A ⟶ B) :
    HasFunctorialProjectiveSurjections.over A ⟶ HasFunctorialProjectiveSurjections.over B :=
  (HasFunctorialProjectiveSurjections.P.map f).left

/-- The chosen projective surjections commute with the functorially induced source maps. -/
@[reassoc]
lemma HasFunctorialProjectiveSurjections.π_naturality {A B : C} (f : A ⟶ B) :
    HasFunctorialProjectiveSurjections.overMap f ≫ HasFunctorialProjectiveSurjections.π B =
      HasFunctorialProjectiveSurjections.π A ≫ f := by
  have hright :
      (HasFunctorialProjectiveSurjections.P.map f).right =
        eqToHom (HasFunctorialProjectiveSurjections.obj_right A) ≫ f ≫
          eqToHom (HasFunctorialProjectiveSurjections.obj_right B).symm := by
    simpa using Functor.congr_hom HasFunctorialProjectiveSurjections.rightFunc_comp_P f
  calc
    HasFunctorialProjectiveSurjections.overMap f ≫ HasFunctorialProjectiveSurjections.π B =
        (HasFunctorialProjectiveSurjections.P.map f).left ≫
          (HasFunctorialProjectiveSurjections.P.obj B).hom ≫
            eqToHom (HasFunctorialProjectiveSurjections.obj_right B) := by
      rfl
    _ = (HasFunctorialProjectiveSurjections.P.obj A).hom ≫
          (HasFunctorialProjectiveSurjections.P.map f).right ≫
            eqToHom (HasFunctorialProjectiveSurjections.obj_right B) := by
      simpa [Category.assoc] using congrArg
        (fun k ↦ k ≫ eqToHom (HasFunctorialProjectiveSurjections.obj_right B))
        (Arrow.w (HasFunctorialProjectiveSurjections.P.map f))
    _ = HasFunctorialProjectiveSurjections.π A ≫ f := by
      rw [hright]
      simp [HasFunctorialProjectiveSurjections.π, Category.assoc]

attribute [simp] HasFunctorialProjectiveSurjections.π_naturality_assoc

/-- The functor of chosen projective sources. -/
def HasFunctorialProjectiveSurjections.overFunctor : C ⥤ C where
  obj A := HasFunctorialProjectiveSurjections.over A
  map f := HasFunctorialProjectiveSurjections.overMap f
  map_id A := by
    exact congrArg Arrow.Hom.left (HasFunctorialProjectiveSurjections.P.map_id A)
  map_comp f g := by
    exact congrArg Arrow.Hom.left (HasFunctorialProjectiveSurjections.P.map_comp f g)

/-- The chosen projective surjections assemble into a natural transformation from the source
objects of the chosen arrows to the identity functor. -/
def HasFunctorialProjectiveSurjections.πNatTrans :
    HasFunctorialProjectiveSurjections.overFunctor ⟶ 𝟭 C where
  app := HasFunctorialProjectiveSurjections.π
  naturality _ _ f := by
    simpa [HasFunctorialProjectiveSurjections.overFunctor] using
      HasFunctorialProjectiveSurjections.π_naturality f

instance HasFunctorialProjectiveSurjections.over_projective (A : C) :
    Projective (HasFunctorialProjectiveSurjections.over A) := by
  exact HasFunctorialProjectiveSurjections.projective_obj A

instance HasFunctorialProjectiveSurjections.π_epi (A : C) :
    Epi (HasFunctorialProjectiveSurjections.π A) := by
  infer_instance

/-- A category with functorial projective surjections determines a left resolution by projective
objects. -/
@[reducible]
def HasFunctorialProjectiveSurjections.toLeftResolution :
    Abelian.LeftResolution (ObjectProperty.ι (isProjective C)) where
  F := (isProjective C).lift HasFunctorialProjectiveSurjections.overFunctor
    HasFunctorialProjectiveSurjections.over_projective
  π := HasFunctorialProjectiveSurjections.πNatTrans
  epi_π_app A := by
    change Epi (HasFunctorialProjectiveSurjections.π A)
    infer_instance

/-- A category with functorial projective surjections has enough projectives. -/
instance : EnoughProjectives C where
  presentation A := ⟨HasFunctorialProjectiveSurjections.presentation A⟩

end HasFunctorialProjectiveSurjections

namespace Abelian.LeftResolution

variable (Λ : LeftResolution (ObjectProperty.ι (isProjective C)))

/-- A left resolution by projective objects gives functorial projective surjections. -/
@[reducible]
def hasFunctorialProjectiveSurjections : HasFunctorialProjectiveSurjections C where
  P :=
    { obj A := Arrow.mk (Λ.π.app A)
      map f := Arrow.homMk' (Λ.F.map f).hom f (by
        simpa using Λ.π.naturality f)
      map_id A := by
        ext <;> simp
      map_comp f g := by
        ext <;> simp }
  rightFunc_comp_P := by
    apply Functor.toPrefunctor_injective
    rfl
  epi_obj A := by
    change Epi (Λ.π.app A)
    infer_instance
  projective_obj A := (Λ.F.obj A).property

/-- A left resolution by projective objects gives enough projectives. -/
theorem toEnoughProjectives (Λ : LeftResolution (ObjectProperty.ι (isProjective C))) :
    EnoughProjectives C := by
  let _ : HasFunctorialProjectiveSurjections C := hasFunctorialProjectiveSurjections Λ
  infer_instance

end Abelian.LeftResolution

end

end CategoryTheory
