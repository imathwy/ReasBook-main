import Mathlib.Algebra.Homology.LeftResolution.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_28_1 (from Chap12) -/
namespace CategoryTheory

universe v u

/- Domain-style sampling for Definition 12.28.1:
- primary domain: projective objects in a category, expressed through lifting across epimorphisms;
- sampled core/canonical declarations:
  `Projective`,
  `Projective.factors`,
  `Projective.factorThru`,
  `EnoughProjectives`;
- best owner abstraction: `Projective P`;
- primitive data: only the object `P : C`;
- derived API: the lifting existence clause `Projective.factors`, the chosen lift
  `Projective.factorThru`, and later chapter packaging such as `EnoughProjectives`;
- source/core/bridge triage:
  `source-facing`: the textbook predicate that an object is projective;
  `core/canonical`: `Projective`;
  `bridge/view`: the explicit lifting property `Projective.factors`.

No local wrapper is needed: the source notion is already owned canonically by `Projective`. -/

variable {C : Type u} [Category.{v} C]

/- Definition 12.28.1: in the chapter's abelian-category setting, an object `P` is projective if
every morphism `P ⟶ B` lifts across every epimorphism `A ⟶ B`; this is the canonical notion
`Projective P`. -/
recall Projective

/- Companion recall: `Projective.factors` is the lifting property for projective objects,
producing for `f : P ⟶ B` and an epimorphism `e : A ⟶ B` a morphism `P ⟶ A` with `f' ≫ e = f`. -/
recall Projective.factors

end CategoryTheory

/-! ### Lemma_12_28_2 (from Chap12) -/
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open CategoryTheory.Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Domain-style sampling:
-- * primary domain: projective objects in an abelian category, detected through `Projective`,
--   `preadditiveCoyonedaObj`, `ShortComplex.ShortExact`, and `Ext`.
-- * inspected owner declarations:
--   `preservesFiniteColimits_preadditiveCoyonedaObj_of_projective`,
--   `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj`,
--   `ShortComplex.ShortExact.splittingOfProjective`,
--   `projective_iff_subsingleton_ext_one`.
-- * layer: `source-facing`; the textbook item is genuinely a four-way equivalence, so the main
--   declaration should stay a local `List.TFAE` rather than collapsing to a bare owner `recall`.
-- * core/canonical owner abstraction: `Projective P`.
-- * primitive data: only the object `P`.
-- * derived API: exactness of `preadditiveCoyonedaObj P`, splitting of short exact sequences
--   ending in `P`, and vanishing of `Ext¹(P, -)`.
-- * the exactness criterion is a `core/canonical` bridge living already in the `[Abelian C]`
--   context, while the full four-way TFAE and the `Ext¹` companion are `source-facing` items
--   that genuinely require `[HasExt C]`.
--
-- The short-exact-sequence clause is quantified directly over the owner object `ShortComplex C`,
-- with `S.X₃ = P` expressing that the sequence ends at `P`; its splitting is recorded through
-- the canonical Prop-level owner `IsSplitEpi S.g` rather than a chosen `S.Splitting`.
--
-- Proof sketch: `(1) ↔ (2)` combines the canonical exactness predicate `exactFunctor` with
-- `exactFunctor_iff`, the finite-limit preservation of `preadditiveCoyonedaObj P`, and the
-- projective criterion `projective_of_preservesFiniteColimits_preadditiveCoyonedaObj`. From `(1)`,
-- any short exact sequence ending in `P` has split epimorphism `g` via
-- `ShortComplex.ShortExact.splittingOfProjective`. Conversely, if every short exact sequence
-- ending in `P` has split epimorphism `g`, then pulling back an arbitrary epimorphism along a map
-- out of `P` yields a split epimorphism onto `P`, so `P` satisfies the lifting property that
-- defines projectivity. The `Ext¹` clause is equivalent to projectivity via
-- `Ext.eq_zero_of_projective` and `projective_iff_subsingleton_ext_one`.
/-- An object is projective exactly when its preadditive co-Yoneda functor is exact. This is the
`(1) ↔ (2)` part of Lemma 12.28.2, stated in the weaker ambient `[Abelian C]` context where no
`Ext`-hypothesis is needed. -/
theorem projective_iff_exact_preadditiveCoyonedaObj (P : C) :
    Projective P ↔ exactFunctor _ _ (preadditiveCoyonedaObj P) := by
  constructor
  · intro hP
    letI : Projective P := hP
    letI : PreservesFiniteColimits (preadditiveCoyonedaObj P) :=
      preservesFiniteColimits_preadditiveCoyonedaObj_of_projective P
    exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩
  · intro hExact
    letI : PreservesFiniteColimits (preadditiveCoyonedaObj P) :=
      (exactFunctor_iff (preadditiveCoyonedaObj P)).1 hExact |>.2
    exact projective_of_preservesFiniteColimits_preadditiveCoyonedaObj P

section

variable [HasExt.{w} C]

/-- Lemma 12.28.2: for an object `P` of an abelian category, the following are equivalent:
`P` is projective, the preadditive co-Yoneda functor `B ↦ Hom(P, B)` is exact, every short exact
sequence `0 ⟶ A ⟶ B ⟶ P ⟶ 0` splits, and every class in `Ext P A 1` vanishes. -/
theorem projective_tfae (P : C) :
    List.TFAE [
      Projective P,
      exactFunctor _ _ (preadditiveCoyonedaObj P),
      ∀ ⦃S : ShortComplex C⦄ (_ : S.X₃ = P) (_ : S.ShortExact), IsSplitEpi S.g,
      ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0
    ] := by
  tfae_have 1 ↔ 2 := by
    simpa using projective_iff_exact_preadditiveCoyonedaObj P
  tfae_have 1 → 3 := by
    intro hP S hX hS
    subst hX
    letI : Projective S.X₃ := hP
    exact (hS.splittingOfProjective).isSplitEpi_g
  tfae_have 3 → 1 := by
    intro hsplit
    refine Projective.mk (fun {E X} f e _ ↦ ?_)
    let q : pullback e f ⟶ P := pullback.snd e f
    let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
    have hS : S.ShortExact := by
      refine { exact := ShortComplex.exact_kernel q }
    letI : IsSplitEpi q := by simpa [S, q] using hsplit rfl hS
    refine ⟨section_ q ≫ pullback.fst e f, ?_⟩
    rw [Category.assoc, pullback.condition]
    change section_ q ≫ q ≫ f = f
    simp
  tfae_have 1 → 4 := by
    intro hP A e
    letI : Projective P := hP
    exact e.eq_zero_of_projective
  tfae_have 4 → 1 := by
    intro hExt
    exact projective_iff_subsingleton_ext_one.2 fun _ ↦
      (subsingleton_iff_forall_eq 0).2 fun e ↦ hExt e
  tfae_finish

/-- Companion projection of `projective_tfae`: an object is projective exactly when every class in
`Ext¹(P, -)` vanishes. -/
theorem projective_iff_ext_one_eq_zero (P : C) :
    Projective P ↔ ∀ ⦃A : C⦄ (e : Ext P A 1), e = 0 :=
  (projective_tfae P).out 0 3

end

end CategoryTheory

/-! ### Lemma_12_28_3 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

section

variable {Ω : Type v}
variable {C : Type u} [Category.{v} C]
variable (P : Ω → C)
variable [HasCoproduct P] [∀ ω, Projective (P ω)]

/- Domain-style sampling in the projective-object owner API:
- primitive owner predicate: `Projective`
- canonical lift across epis: `Projective.factorThru`
- owner stability under isomorphism: `Projective.of_iso`
- owner coproduct closure: the instance `Projective (∐ P)` in
  `Mathlib.CategoryTheory.Preadditive.Projective.Basic`
- best owner abstraction: `Projective (∐ P)`
- primitive data: a family `P : Ω → C` with a coproduct and objectwise projectivity
- derived API: the canonical instance exhibiting the coproduct itself as projective
- source/core/bridge triage:
  `source-facing`: the textbook lemma that a coproduct of projective objects is projective
  `core/canonical`: the upstream instance `Projective (∐ P)`
  `bridge/view`: none needed here

Lemma 12.28.3 is a `core/canonical` recall item: the source statement is exactly the upstream owner
instance asserting that a coproduct of projective objects is projective. The ambient abelian
hypothesis from the textbook is redundant for this canonical construction, so the refined Lean
interface keeps only the categorical data actually used by the owner abstraction.
-/
#check (inferInstance : Projective (∐ P))

end

end CategoryTheory

/-! ### Definition_12_28_4 (from Chap12) -/
namespace CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling in the projective/enough-projectives domain:
- mathlib primitive objectwise witness: `ProjectivePresentation X`
- mathlib ambient owner abstraction: `EnoughProjectives C`
- mathlib owner field producing those witnesses: `EnoughProjectives.presentation`
- mathlib owner-derived chosen API under `[EnoughProjectives C]`: `Projective.over X`, `Projective.π X`
- chapter bridge from source-facing left resolutions:
  `CategoryTheory.Abelian.LeftResolution.toEnoughProjectives`

Source/core/bridge triage for Definition 12.28.4:
- source-facing: every object of `C` admits an epimorphism from a projective object.
- core/canonical: `EnoughProjectives C`.
- bridge/view: `EnoughProjectives.presentation` supplies the primitive objectwise witness
  `ProjectivePresentation X`, while `Projective.over X` and `Projective.π X` are the derived
  chosen-object API obtained from the owner abstraction.

Definition 12.28.4 is therefore a `core/canonical` recall item: the textbook notion is already the
mathlib owner class `EnoughProjectives`, so this file should reuse that owner abstraction directly
instead of introducing a parallel wrapper. -/
recall EnoughProjectives

/- Companion recall: the primitive data of `EnoughProjectives C` is
`EnoughProjectives.presentation`, witnessing `Nonempty (ProjectivePresentation X)` for each
`X : C`. -/
recall EnoughProjectives.presentation

/- Companion recall: the primitive objectwise witness for one object is a
`ProjectivePresentation X`. -/
recall ProjectivePresentation

section

variable [EnoughProjectives C]

/- Companion recall: under enough projectives, `Projective.over X` is a chosen projective object
mapping onto `X`. -/
recall Projective.over

/- Companion recall: under enough projectives, `Projective.π X` is the chosen epimorphism
`Projective.over X ⟶ X`. -/
recall Projective.π

end

end

end CategoryTheory

/-! ### Definition_12_28_5 (from Chap12) -/
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
