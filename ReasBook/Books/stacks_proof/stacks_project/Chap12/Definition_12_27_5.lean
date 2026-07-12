import Mathlib

namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.27.5:
- primary domain: injective presentations together with functorial choices of injective
  embeddings;
- sampled core/canonical declarations:
  `InjectivePresentation`,
  `EnoughInjectives`,
  `EnoughInjectives.presentation`,
  `CategoryTheory.IsGrothendieckAbelian.monoMapFactorizationDataRlp`,
  `NatTrans`;
- best owner abstraction: the source-facing owner is
  `HasFunctorialInjectiveEmbeddings C`, with categorical functoriality exposed by a target
  functor and a natural transformation from the identity functor;
- primitive data: a functor `J : C ⥤ Arrow C`, a proof `J ⋙ Arrow.leftFunc = 𝟭 C`, and the
  objectwise facts that each `J.obj A` is mono with injective target;
- derived API: the canonical objectwise `InjectivePresentation`, the views `under`, `ι`, and
  `underMap`, their naturality square, and the canonical bridge to `EnoughInjectives`.

Source/core/bridge triage for Definition 12.27.5:
- source-facing: `HasFunctorialInjectiveEmbeddings C`, recording a functorial choice of injective
  embeddings.
- core/canonical: `InjectivePresentation` and `EnoughInjectives`, which already own the underlying
  objectwise embedding data in mathlib.
- bridge/view: the canonical objectwise map to `InjectivePresentation`, the induced instance
  `HasFunctorialInjectiveEmbeddings C → EnoughInjectives C`, and, under Grothendieck-abelian
  hypotheses, the canonical functorial factorization bridge
  `IsGrothendieckAbelian C → HasFunctorialInjectiveEmbeddings C`.

The owner abstraction for the objectwise data is `InjectivePresentation`; this file should not keep
parallel public wrappers for those chosen presentations. A bare `EnoughInjectives C` hypothesis
does not canonically determine a functorial arrow functor, so the generic converse bridge is
intentionally absent; when a genuine functorial owner exists upstream, such as the Grothendieck
small-object factorization data, this file should reuse that owner directly. -/

/-- Definition 12.27.5, formalized without the redundant abelianity assumption: a category has
functorial injective embeddings if it is equipped with a functor `J : C ⥤ Arrow C` whose source
functor is the identity, so that `J.obj A`
is a functorial choice of injective presentation of `A`. Concretely, each arrow `J.obj A` is a
monomorphism and each target `(J.obj A).right` is injective. -/
@[stacks 0139]
class HasFunctorialInjectiveEmbeddings (C : Type u) [Category.{v} C] where
  J : C ⥤ Arrow C
  leftFunc_comp_J : J ⋙ Arrow.leftFunc = 𝟭 C
  mono_obj (A : C) : Mono ((J.obj A).hom)
  injective_obj (A : C) : Injective ((J.obj A).right)

attribute [instance] HasFunctorialInjectiveEmbeddings.mono_obj
attribute [instance] HasFunctorialInjectiveEmbeddings.injective_obj

namespace NatTrans

/-- The natural transformation `η : 𝟭 C ⟶ F` viewed objectwise as an arrow of `C`, functorially in
the source object. This is the canonical bridge from an identity-based natural transformation to
the `Arrow`-valued data used by `HasFunctorialInjectiveEmbeddings`. -/
noncomputable def arrowFunctor {C : Type u} [Category.{v} C] {F : C ⥤ C} (η : 𝟭 C ⟶ F) :
    C ⥤ Arrow C where
  obj X := Arrow.mk (η.app X)
  map f := Arrow.homMk' f (F.map f) (η.naturality f)
  map_id X := by
    apply Arrow.hom_ext <;> simp
  map_comp f g := by
    apply Arrow.hom_ext <;> simp

@[simp] theorem arrowFunctor_leftFunc_comp {C : Type u} [Category.{v} C] {F : C ⥤ C}
    (η : 𝟭 C ⟶ F) :
    η.arrowFunctor ⋙ Arrow.leftFunc = 𝟭 C :=
  rfl

end NatTrans

section

variable {C : Type u} [Category.{v} C] [HasFunctorialInjectiveEmbeddings C]

/-- The source of the chosen arrow `J.obj A` is canonically `A`. -/
@[simp]
private lemma HasFunctorialInjectiveEmbeddings.obj_left (A : C) :
    (HasFunctorialInjectiveEmbeddings.J.obj A).left = A := by
  simpa using Functor.congr_obj HasFunctorialInjectiveEmbeddings.leftFunc_comp_J A

/-- The chosen injective object under `A`. -/
abbrev HasFunctorialInjectiveEmbeddings.under (A : C) : C :=
  (HasFunctorialInjectiveEmbeddings.J.obj A).right

/-- The chosen functorial injective embedding of `A`. -/
abbrev HasFunctorialInjectiveEmbeddings.ι (A : C) :
    A ⟶ HasFunctorialInjectiveEmbeddings.under A :=
  eqToHom (HasFunctorialInjectiveEmbeddings.obj_left A).symm ≫
    (HasFunctorialInjectiveEmbeddings.J.obj A).hom

/-- The map between chosen injective targets induced by a morphism. -/
abbrev HasFunctorialInjectiveEmbeddings.underMap {A B : C} (f : A ⟶ B) :
    HasFunctorialInjectiveEmbeddings.under A ⟶ HasFunctorialInjectiveEmbeddings.under B :=
  (HasFunctorialInjectiveEmbeddings.J.map f).right

/-- The canonical injective presentation determined by the chosen functorial injective embedding of
`A`. -/
def HasFunctorialInjectiveEmbeddings.presentation (A : C) : InjectivePresentation A where
  J := HasFunctorialInjectiveEmbeddings.under A
  injective := HasFunctorialInjectiveEmbeddings.injective_obj A
  f := HasFunctorialInjectiveEmbeddings.ι A
  mono := by infer_instance

/-- The chosen embeddings and functorially induced target maps form a commutative square. -/
lemma HasFunctorialInjectiveEmbeddings.ι_naturality {A B : C} (f : A ⟶ B) :
    CommSq
      f
      (HasFunctorialInjectiveEmbeddings.ι A)
      (HasFunctorialInjectiveEmbeddings.ι B)
      (HasFunctorialInjectiveEmbeddings.underMap f) := by
  have hleft :
      (HasFunctorialInjectiveEmbeddings.J.map f).left =
        eqToHom (HasFunctorialInjectiveEmbeddings.obj_left A) ≫ f ≫
          eqToHom (HasFunctorialInjectiveEmbeddings.obj_left B).symm := by
    simpa using Functor.congr_hom HasFunctorialInjectiveEmbeddings.leftFunc_comp_J f
  refine CommSq.mk ?_
  calc
    f ≫ HasFunctorialInjectiveEmbeddings.ι B =
        eqToHom (HasFunctorialInjectiveEmbeddings.obj_left A).symm ≫
          (HasFunctorialInjectiveEmbeddings.J.map f).left ≫
            (HasFunctorialInjectiveEmbeddings.J.obj B).hom := by
      simp [HasFunctorialInjectiveEmbeddings.ι, hleft, Category.assoc]
    _ =
        eqToHom (HasFunctorialInjectiveEmbeddings.obj_left A).symm ≫
          (HasFunctorialInjectiveEmbeddings.J.obj A).hom ≫
            HasFunctorialInjectiveEmbeddings.underMap f := by
      simpa [HasFunctorialInjectiveEmbeddings.underMap, Category.assoc] using
        congrArg (fun k ↦ eqToHom (HasFunctorialInjectiveEmbeddings.obj_left A).symm ≫ k)
          (Arrow.w (HasFunctorialInjectiveEmbeddings.J.map f)).symm
    _ = HasFunctorialInjectiveEmbeddings.ι A ≫ HasFunctorialInjectiveEmbeddings.underMap f := by
      simp [HasFunctorialInjectiveEmbeddings.ι, Category.assoc]

/-- Equality form of `HasFunctorialInjectiveEmbeddings.ι_naturality` for `Arrow.homMk` and
reassociation. -/
@[reassoc]
lemma HasFunctorialInjectiveEmbeddings.ι_naturality_w {A B : C} (f : A ⟶ B) :
    f ≫ HasFunctorialInjectiveEmbeddings.ι B =
      HasFunctorialInjectiveEmbeddings.ι A ≫ HasFunctorialInjectiveEmbeddings.underMap f :=
  (HasFunctorialInjectiveEmbeddings.ι_naturality f).w

attribute [simp] HasFunctorialInjectiveEmbeddings.ι_naturality_w

instance HasFunctorialInjectiveEmbeddings.under_injective (A : C) :
    Injective (HasFunctorialInjectiveEmbeddings.under A) := by
  simpa [HasFunctorialInjectiveEmbeddings.under] using
    HasFunctorialInjectiveEmbeddings.injective_obj A

instance HasFunctorialInjectiveEmbeddings.ι_mono (A : C) :
    Mono (HasFunctorialInjectiveEmbeddings.ι A) := by
  simpa [HasFunctorialInjectiveEmbeddings.ι] using
    (inferInstance :
      Mono
        (eqToHom (HasFunctorialInjectiveEmbeddings.obj_left A).symm ≫
          (HasFunctorialInjectiveEmbeddings.J.obj A).hom))

end

section IsGrothendieckAbelian

open MorphismProperty
open ZeroObject

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian C]

/-- The functor sending an object to its zero morphism into the zero object. -/
private noncomputable def zeroArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : X ⟶ (0 : C))
  map {X Y} f := Arrow.homMk f (0 : (0 : C) ⟶ (0 : C)) (by simp)
  map_id X := by
    ext
    · rfl
    · simp
  map_comp f g := by
    ext
    · rfl
    · simp

/-- The canonical injective-presentation arrow in a Grothendieck abelian category, obtained by
functorially factoring the zero map as a mono followed by an injective object. -/
private noncomputable def grothendieckInjectiveArrow (X : C) : Arrow C :=
  Arrow.mk (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : X ⟶ (0 : C))).i

/-- The functorial map between the canonical injective targets of two objects in a Grothendieck
abelian category. -/
private noncomputable def grothendieckInjectiveArrowMap {X Y : C} (f : X ⟶ Y) :
    grothendieckInjectiveArrow X ⟶ grothendieckInjectiveArrow Y :=
  let data := functorialFactorizationData (monomorphisms C) (monomorphisms C).rlp
  let φ : Arrow.mk (0 : X ⟶ (0 : C)) ⟶ Arrow.mk (0 : Y ⟶ (0 : C)) := zeroArrowFunctor.map f
  Arrow.homMk f (data.mapZ φ) <| by
    exact (data.i_mapZ φ).symm

/-- A Grothendieck abelian category admits functorial injective embeddings via the canonical
small-object factorization of the zero morphism. -/
@[reducible]
noncomputable def hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian :
    HasFunctorialInjectiveEmbeddings C where
  J :=
    { obj := grothendieckInjectiveArrow
      map := grothendieckInjectiveArrowMap
      map_id := by
        intro X
        ext
        · rfl
        ·
          simpa [grothendieckInjectiveArrowMap, grothendieckInjectiveArrow, zeroArrowFunctor] using
            (functorialFactorizationData (monomorphisms C) (monomorphisms C).rlp).mapZ_id
              (0 : X ⟶ (0 : C))
      map_comp := by
        intro X Y Z f g
        ext
        · rfl
        ·
          dsimp [grothendieckInjectiveArrowMap]
          rw [show zeroArrowFunctor.map (f ≫ g) = zeroArrowFunctor.map f ≫ zeroArrowFunctor.map g by
            simpa using (zeroArrowFunctor.map_comp f g)]
          exact
            (functorialFactorizationData (monomorphisms C) (monomorphisms C).rlp).mapZ_comp
              (zeroArrowFunctor.map f) (zeroArrowFunctor.map g) }
  leftFunc_comp_J := rfl
  mono_obj X := by
    change Mono (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : X ⟶ (0 : C))).i
    infer_instance
  injective_obj X := by
    change Injective (IsGrothendieckAbelian.monoMapFactorizationDataRlp (0 : X ⟶ (0 : C))).Z
    infer_instance

end IsGrothendieckAbelian

section HasFunctorialInjectiveEmbeddings

variable {C : Type u} [Category.{v} C] [HasFunctorialInjectiveEmbeddings C]

/-- A category with functorial injective embeddings has enough injectives. -/
instance : EnoughInjectives C where
  presentation A := ⟨HasFunctorialInjectiveEmbeddings.presentation A⟩

end HasFunctorialInjectiveEmbeddings

end CategoryTheory
