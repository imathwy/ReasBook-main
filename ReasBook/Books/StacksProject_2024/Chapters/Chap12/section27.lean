import Mathlib
import Mathlib.CategoryTheory.Abelian.Injective.Basic
import Mathlib.CategoryTheory.Abelian.Injective.Dimension
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_27_1 (from Chap12) -/
namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.27.1:
- primary domain: injective objects in a category, expressed through extension across
  monomorphisms;
- sampled core/canonical declarations:
  `Injective`,
  `Injective.factors`,
  `Injective.factorThru`;
- best owner abstraction: `Injective J`;
- primitive data: only the object `J : C`;
- derived API: the extension existence clause `Injective.factors` and the chosen extension
  `Injective.factorThru`;
- source/core/bridge triage:
  `source-facing`: the textbook predicate that an object is injective;
  `core/canonical`: `Injective`;
  `bridge/view`: the explicit extension property `Injective.factors`.

No local wrapper is needed: the source notion is already owned canonically by `Injective`. -/

variable {C : Type u} [Category.{v} C]

/- Definition 12.27.1: an object `J` is injective if every morphism `A ⟶ J` extends across every
monomorphism `A ⟶ B`; this is the canonical notion `Injective J`. -/
recall Injective

/- Companion recall: `Injective.factors` is the extension property for injective objects,
producing for `g : A ⟶ J` and a monomorphism `f : A ⟶ B` a morphism `B ⟶ J` with `f ≫ h = g`. -/
recall Injective.factors

end CategoryTheory

/-! ### Lemma_12_27_2 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

-- Domain-style sampling:
-- * primary domain: injective objects in an abelian category, detected through `Injective`,
--   `preadditiveYonedaObj`, `ShortComplex.ShortExact`, and `Ext`.
-- * inspected owner declarations:
--   `preservesFiniteColimits_preadditiveYonedaObj_of_injective`,
--   `injective_of_preservesFiniteColimits_preadditiveYonedaObj`,
--   `ShortComplex.ShortExact.splittingOfInjective`,
--   `injective_iff_subsingleton_ext_one`.
-- * layer: `source-facing`; the textbook item is genuinely a four-way equivalence, so the main
--   declaration should stay a local `List.TFAE` rather than collapsing to a bare owner `recall`.
-- * core/canonical owner abstraction: `Injective I`.
-- * primitive data: only the object `I`.
-- * derived API: exactness of `preadditiveYonedaObj I`, the split-mono formulation of short exact
--   sequences beginning at `I`, and vanishing of `Ext¹(-, I)`.
--
-- The short-exact-sequence clause is quantified directly over the owner object `ShortComplex C`,
-- with `S.X₁ = I` expressing that the sequence starts at `I`; its splitting is recorded through
-- the canonical Prop-level owner `IsSplitMono S.f` rather than a chosen `S.Splitting`.
--
-- Proof sketch: `(1) ↔ (2)` combines the canonical exactness predicate `exactFunctor` with
-- `exactFunctor_iff`, the finite-limit preservation of `preadditiveYonedaObj I`, and the injective
-- criterion `injective_of_preservesFiniteColimits_preadditiveYonedaObj`. From `(1)`, any short
-- exact sequence starting at `I` has split mono `f` via
-- `ShortComplex.ShortExact.splittingOfInjective`. Conversely, if every short exact sequence
-- starting at `I` has split mono `f`, then pushing out an arbitrary monomorphism along a map into
-- `I` yields a split monomorphism `I ⟶ pushout g f`, hence a retraction that exhibits the
-- extension property defining injectivity. The `Ext¹` clause is equivalent to injectivity via
-- `Ext.eq_zero_of_injective` and `injective_iff_subsingleton_ext_one`.
/-- Lemma 12.27.2: for an object `I` of an abelian category, the following are equivalent:
`I` is injective, the preadditive Yoneda functor `B ↦ Hom(B, I)` is exact, every short exact
sequence `0 ⟶ I ⟶ A ⟶ B ⟶ 0` splits, and every class in `Ext B I 1` vanishes. -/
theorem injective_tfae (I : C) :
    List.TFAE [
      Injective I,
      exactFunctor _ _ (preadditiveYonedaObj I),
      ∀ ⦃S : ShortComplex C⦄ (_ : S.X₁ = I) (_ : S.ShortExact), IsSplitMono S.f,
      ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0
    ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hI
      letI : Injective I := hI
      letI : PreservesFiniteColimits (preadditiveYonedaObj I) :=
        preservesFiniteColimits_preadditiveYonedaObj_of_injective I
      exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
    · intro hExact
      letI : PreservesFiniteColimits (preadditiveYonedaObj I) :=
        (exactFunctor_iff (preadditiveYonedaObj I)).1 hExact |>.2
      exact injective_of_preservesFiniteColimits_preadditiveYonedaObj I
  tfae_have 1 → 3 := by
    intro hI S hX hS
    subst hX
    letI : Injective S.X₁ := hI
    exact (hS.splittingOfInjective).isSplitMono_f
  tfae_have 3 → 1 := by
    intro hsplit
    refine Injective.mk ?_
    intro X Y g f _
    let i : I ⟶ pushout g f := pushout.inl g f
    let S := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance
    have hs : IsSplitMono i := by
      simpa [S, i] using hsplit rfl hS
    letI : IsSplitMono i := hs
    refine ⟨pushout.inr g f ≫ retraction i, ?_⟩
    calc
      f ≫ pushout.inr g f ≫ retraction i = g ≫ i ≫ retraction i := by
        simpa [i, Category.assoc] using congrArg (fun k ↦ k ≫ retraction i)
          (show g ≫ pushout.inl g f = f ≫ pushout.inr g f from pushout.condition).symm
      _ = g := by simp [i]
  tfae_have 1 → 4 := by
    intro hI B e
    letI : Injective I := hI
    exact e.eq_zero_of_injective
  tfae_have 4 → 1 := by
    intro hExt
    rw [injective_iff_subsingleton_ext_one]
    intro B
    exact (subsingleton_iff_forall_eq 0).2 fun e ↦ hExt e
  tfae_finish

/-- Companion projection of `injective_tfae`: an object is injective exactly when its
preadditive Yoneda functor is exact. -/
theorem injective_iff_exact_preadditiveYonedaObj (I : C) :
    Injective I ↔ exactFunctor _ _ (preadditiveYonedaObj I) :=
  (injective_tfae I).out 0 1

/-- Companion projection of `injective_tfae`: an object is injective exactly when every class in
`Ext¹(-, I)` vanishes. -/
theorem injective_iff_ext_one_eq_zero (I : C) :
    Injective I ↔ ∀ ⦃B : C⦄ (e : Ext B I 1), e = 0 :=
  (injective_tfae I).out 0 3

end CategoryTheory

/-! ### Lemma_12_27_3 (from Chap12) -/
open CategoryTheory Limits

universe v u u'

section

variable {C : Type u} [Category.{v} C]
variable {Ω : Type u'} (I : Ω → C) [HasProduct I] [∀ ω, Injective (I ω)]

/- Domain-style sampling for Lemma 12.27.3:
- primary domain: injective objects in a category, together with their stability under products;
- sampled owner API:
  `Injective`,
  `Injective.factors`,
  `Injective.factorThru`,
  the product instance `Injective (∏ᶜ I)` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`;
- best owner abstraction: `Injective (∏ᶜ I)`;
- primitive data: only the family `I`, the product existence hypothesis `[HasProduct I]`, and the
  objectwise injective instances `[∀ ω, Injective (I ω)]`;
- derived API: the injective structure on the product itself, obtained canonically by instance
  synthesis.

This item is a `core/canonical` recall: the textbook statement is exactly the upstream owner
instance that products of injective objects are injective, so no local wrapper theorem is needed.
-/

/- Lemma 12.27.3: if `I : Ω → C` is a family of injective objects and the product `∏ᶜ I`
exists, then `∏ᶜ I` is injective. This is exactly the canonical product instance for
`Injective`. -/
#synth Injective (∏ᶜ I)

end

/-! ### Definition_12_27_4 (from Chap12) -/
namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.27.4:
- primary domain: injective presentations and the category-level predicate of having enough
  injectives;
- sampled core/canonical declarations:
  `InjectivePresentation`,
  `EnoughInjectives`,
  `EnoughInjectives.presentation`;
- best owner abstraction: `EnoughInjectives C`;
- primitive data: for each object `X : C`, the existence datum
  `Nonempty (InjectivePresentation X)`;
- derived API: the owner field `EnoughInjectives.presentation X`.

This item is `core/canonical`: the source notion is already owned by mathlib's
`EnoughInjectives`, so the file should remain a direct recall rather than introducing a local
wrapper or alias. -/

section

variable {C : Type u} [Category.{v} C]

/- Definition 12.27.4: the owner abstraction for "having enough injectives" is
`EnoughInjectives C`, meaning every object of `C` admits an injective presentation. -/
recall EnoughInjectives

/- Companion recall: the primitive data of `EnoughInjectives C` is
`EnoughInjectives.presentation`, witnessing `Nonempty (InjectivePresentation X)` for each
`X : C`. -/
recall EnoughInjectives.presentation

end

end CategoryTheory

/-! ### Definition_12_27_5 (from Chap12) -/
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
