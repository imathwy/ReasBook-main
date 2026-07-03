import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Subcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Proposition_13_23_1 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open CochainComplex
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Proposition 13.23.1:
- primary domain: bounded-below homotopy and derived categories, with the injective full
  subcategory as a source-facing bridge into the canonical localization functor;
- sampled owner declarations:
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `mapBoundedBelowHomotopyToDerivedBelow`,
  `HomotopyResolutionFunctor`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedBelow_injective`;
- best owner abstraction: the proposition is about the canonical composite
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyToDerivedBelow`, not about a new
  owner functor alias;
- primitive vs. derived API:
  primitive data: the injective full subcategory `K⁺ᵢ(𝒜)`, the localization functor
    `mapBoundedBelowHomotopyToDerivedBelow`, and a homotopy resolution functor;
  derived API: the factorization of a homotopy resolution through `D⁺(𝒜)` and the resulting
    equivalence statement.

Source/core/bridge triage:
- `source-facing`: Proposition 13.23.1 itself, asserting that bounded-below injective complexes
  compute `D⁺(𝒜)`;
- `core/canonical`: `Functor.IsLocalization`, `Localization.lift`, and the hom-bijection into
  bounded-below injective complexes;
-/

local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "KinjIncl" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜))
local notation "IToD" => KinjIncl ⋙ Q

attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace HomotopyResolutionFunctor

theorem isInvertedBy (j : HomotopyResolutionFunctor 𝒜) :
    MorphismProperty.IsInvertedBy (Qis⁺(𝒜)) j.toFunctor := by
  sorry

noncomputable abbrev lift (j : HomotopyResolutionFunctor 𝒜) :
    D⁺(𝒜) ⥤ K⁺ᵢ(𝒜) :=
  Localization.lift j.toFunctor (isInvertedBy j) Q

noncomputable abbrev liftCompIso (j : HomotopyResolutionFunctor 𝒜) :
    Q ⋙ j.lift ≅ j.toFunctor :=
  Localization.fac j.toFunctor (isInvertedBy j) Q

private noncomputable def toDerivedIso (j : HomotopyResolutionFunctor 𝒜) :
    Q ≅ j.toFunctor ⋙ IToD := by
  let τ : Q ⟶ j.toFunctor ⋙ IToD :=
    (Functor.leftUnitor Q).inv ≫ Functor.whiskerRight j.ι Q ≫
      (Functor.associator j.toFunctor KinjIncl Q).hom
  have hτ : ∀ X, IsIso (τ.app X) := by
    intro X
    haveI : IsIso ((Functor.whiskerRight j.ι Q).app X) := by
      simpa using (Localization.inverts Q (Qis⁺(𝒜)) _ (j.quasiIso_app X))
    change IsIso ((Functor.leftUnitor Q).inv.app X ≫
      (Functor.whiskerRight j.ι Q).app X ≫
      (Functor.associator j.toFunctor KinjIncl Q).hom.app X)
    infer_instance
  exact NatIso.ofComponents (fun X ↦ asIso (τ.app X)) (fun f ↦ τ.naturality f)

noncomputable def lift_unitIso (j : HomotopyResolutionFunctor 𝒜) :
    𝟭 (D⁺(𝒜)) ≅ j.lift ⋙ IToD := by
  let e : Q ≅ Q ⋙ (j.lift ⋙ IToD) :=
    j.toDerivedIso ≪≫
      Functor.isoWhiskerRight (j.liftCompIso).symm IToD ≪≫
      Functor.associator Q j.lift IToD
  exact
    Localization.liftNatIso Q (Qis⁺(𝒜)) Q (Q ⋙ (j.lift ⋙ IToD)) (𝟭 (D⁺(𝒜)))
      (j.lift ⋙ IToD) e

end HomotopyResolutionFunctor

private theorem iToD_map_bijective (X Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (((ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜)) ⋙
          mapBoundedBelowHomotopyToDerivedBelow).map : (X ⟶ Y) → _) := by
  let Q' : K⁺(𝒜) ⥤ D⁺(𝒜) := mapBoundedBelowHomotopyToDerivedBelow
  let KinjIncl' : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
    ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  let IToD' : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := KinjIncl' ⋙ Q'
  let KplusIncl := (ObjectProperty.ι (HomotopyCategory.plus 𝒜) : K⁺(𝒜) ⥤ _)
  let Qplus := KplusIncl ⋙ DerivedCategory.Qh
  let DplusIncl := (ObjectProperty.ι (t.plus : ObjectProperty (D(𝒜))) : D⁺(𝒜) ⥤ _)
  let hIncl :
      Function.Bijective
        (KinjIncl'.map : (X ⟶ Y) → (X.obj ⟶ Y.obj)) := by
    simpa [KinjIncl'] using (Functor.FullyFaithful.ofFullyFaithful KinjIncl').map_bijective X Y
  let hQ :
      Function.Bijective
        (Q'.map : (X.obj ⟶ Y.obj) → (Q'.obj X.obj ⟶ Q'.obj Y.obj)) := by
    let hAmbient :
        Function.Bijective
          (Qplus.map :
            (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      let hKplusIncl :
          Function.Bijective
            (KplusIncl.map :
              (X.obj ⟶ Y.obj) → (X.obj.obj ⟶ Y.obj.obj)) := by
        simpa using
          (Functor.FullyFaithful.ofFullyFaithful KplusIncl).map_bijective X.obj Y.obj
      let hQh :
          Function.Bijective
            (DerivedCategory.Qh.map :
              (X.obj.obj ⟶ Y.obj.obj) →
                (DerivedCategory.Qh.obj X.obj.obj ⟶ DerivedCategory.Qh.obj Y.obj.obj)) := by
        let X' : K⁺(𝒜) := X.obj
        simpa using
          homotopyCategory_to_derived_bijective_of_boundedBelow_injective X'.obj.as
            Y.toInjectivePlus
      simpa [Functor.comp_map] using hQh.comp hKplusIncl
    let hDplusIncl :
        Function.Bijective
          (DplusIncl.map :
            (Q'.obj X.obj ⟶ Q'.obj Y.obj) →
              (DplusIncl.obj (Q'.obj X.obj) ⟶ DplusIncl.obj (Q'.obj Y.obj))) := by
      simpa using
        (Functor.FullyFaithful.ofFullyFaithful DplusIncl).map_bijective
          (Q'.obj X.obj) (Q'.obj Y.obj)
    have hcomp :
        DplusIncl.map ∘
            (Q'.map : (X.obj ⟶ Y.obj) → (Q'.obj X.obj ⟶ Q'.obj Y.obj)) =
          (Qplus.map : (X.obj ⟶ Y.obj) → (Qplus.obj X.obj ⟶ Qplus.obj Y.obj)) := by
      funext f
      rfl
    exact (Function.Bijective.of_comp_iff' hDplusIncl _).mp (hcomp ▸ hAmbient)
  simpa [IToD', Q', KinjIncl', Functor.comp_map] using hQ.comp hIncl

namespace HomotopyResolutionFunctor

/-- Proposition 13.23.1, canonical owner form: for any homotopy resolution functor
`j : K^+(\mathcal A) ⥤ K^+(\mathcal I)`, the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)` is an equivalence of categories. -/
theorem toDerived_isEquivalence (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence
      (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
        mapBoundedBelowHomotopyToDerivedBelow) := by
  let F : K⁺ᵢ(𝒜) ⥤ D⁺(𝒜) := IToD
  obtain ⟨hFF⟩ :
      Nonempty F.FullyFaithful := by
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    simpa [F] using iToD_map_bijective X Y
  let _ : F.Full := hFF.full
  let _ : F.Faithful := hFF.faithful
  simpa [F] using F.fully_faithful_isEquivalence_of_objwise_iso
    (fun X ↦ j.lift.obj X) (fun X ↦ (j.lift_unitIso).app X)

end HomotopyResolutionFunctor

-- Proof sketch: essential surjectivity is obtained by choosing bounded-below injective
-- resolutions in the presence of enough injectives, while full faithfulness follows from the
-- bijection between homotopy and derived morphisms into bounded-below injective complexes.
/-- Proposition 13.23.1: if an abelian category `𝒜` has enough injectives, then the canonical
functor `K^+(\mathcal I) ⥤ D^+(\mathcal A)` from bounded-below complexes of injective objects to
the bounded-below derived category is an equivalence of categories. -/
theorem boundedBelowInjectiveHomotopyToDerived_isEquivalence [EnoughInjectives 𝒜] :
    Functor.IsEquivalence
      (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
        mapBoundedBelowHomotopyToDerivedBelow) := by
  obtain ⟨j⟩ : Nonempty (HomotopyResolutionFunctor 𝒜) := exists_homotopyResolutionFunctor
  simpa using j.toDerived_isEquivalence

end

end CategoryTheory

/-! ### Definition_13_23_2 (from Chap13) -/
open CategoryTheory

universe v u

namespace CochainComplex

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: bounded-below injective resolutions of cochain complexes;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.injective`,
  `CochainComplex.InjectiveResolution.quasiIso`,
  `CategoryTheory.HomotopyResolutionFunctor`;
- best owner abstraction: `CochainComplex.InjectiveResolution` already owns the chosen resolving
  complex, comparison map, bounded-below structure, and termwise-injective/quasi-isomorphism API
  for a single bounded-below complex;
- primitive data here: only the objectwise assignment `K ↦ InjectiveResolution K`;
- derived API here: the chosen complex, the comparison map, and the basic resolution facts, all of
  which should be read directly from the owner `InjectiveResolution` instead of being re-exported
  under parallel local names.

Source/core/bridge triage:
- `source-facing`: `ResolutionFunctorOne` is the Stacks-definition objectwise choice of bounded-
  below injective resolutions;
- `core/canonical`: `CochainComplex.InjectiveResolution` is the project owner for the data of a
  chosen injective resolution of one complex;
- `bridge/view`: later files build the homotopy-category realization from this objectwise choice.
-/
/-- Definition 13.23.2: a resolution functor 1 on an abelian category assigns to each
bounded-below cochain complex `K : Plus 𝒜` a chosen bounded-below injective resolution of
`K`, namely an element of the canonical owner `InjectiveResolution K.obj`. -/
abbrev ResolutionFunctorOne :=
  (K : Plus 𝒜) → InjectiveResolution K.obj

end CochainComplex

/-! ### Lemma_13_23_3 (from Chap13) -/
open CategoryTheory
open ComplexShape
open scoped CategoryTheory

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-
Domain-style sampling:
- primary domain: bounded-below injective resolutions viewed in the bounded-below homotopy
  category;
- sampled owner declarations:
  `CochainComplex.ResolutionFunctorOne`,
  `CategoryTheory.HomotopyResolutionFunctor`,
  `CategoryTheory.ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)`,
  `CochainComplex.InjectivePlus.toHomotopy`,
  `HomotopyCategory.Plus.quotient`;
- best owner abstraction: `CategoryTheory.HomotopyResolutionFunctor` is the canonical owner for
  the homotopy-category realization, while `ResolutionFunctorOne` is only the source-facing
  objectwise choice of injective resolutions;
- primitive data: `R : ResolutionFunctorOne 𝒜`;
- derived API: the induced object of `K^+(\mathcal I)`, the comparison morphism in
  `K^+(\mathcal A)`, and the bridge predicate comparing `R` with a homotopy resolution
  functor through explicit objectwise isomorphisms in `K^+(\mathcal I)`.

Source/core/bridge triage:
- `source-facing`: `ResolutionFunctorOne 𝒜`;
- `core/canonical`: `CategoryTheory.HomotopyResolutionFunctor 𝒜`;
- `bridge/view`: `ResolutionFunctorOne.homotopyObj`, `ResolutionFunctorOne.homotopyι`, and
  `ResolutionFunctorOne.RealizedBy`.
-/
namespace ResolutionFunctorOne

local notation "Qplus" => HomotopyCategory.Plus.quotient 𝒜
local notation "KinjIncl" =>
  ObjectProperty.ι (CategoryTheory.boundedBelowInjectiveHomotopyProperty 𝒜)

/-- The chosen injective resolution `j(K)` viewed as an object of `K^+(\mathcal I)`. -/
abbrev homotopyObj (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    K⁺ᵢ(𝒜) :=
  ⟨(Qplus).obj (R K : Plus 𝒜), fun n ↦ by
    simpa using (R K).injective n⟩

/-- The comparison map `K ⟶ j(K)` viewed in `K^+(\mathcal A)`. -/
abbrev homotopyι (R : ResolutionFunctorOne 𝒜) (K : Plus 𝒜) :
    (Qplus).obj K ⟶ (KinjIncl).obj (R.homotopyObj K) :=
  (Qplus).map ⟨(R K).ι⟩

/-- A homotopy resolution functor realizes `R` when, on each bounded-below complex `K`, its
value is canonically isomorphic to the chosen object `j(K)`, and after transporting along that
isomorphism its comparison morphism agrees in `K^+(\mathcal A)` with the chosen
quasi-isomorphism `K ⟶ j(K)`. -/
def RealizedBy (R : ResolutionFunctorOne 𝒜)
    (j : HomotopyResolutionFunctor 𝒜) : Prop :=
  ∀ K : Plus 𝒜, ∃! eK : j.toFunctor.obj ((Qplus).obj K) ≅ R.homotopyObj K,
    j.ι.app ((Qplus).obj K) ≫ (KinjIncl).map eK.hom = homotopyι R K

end ResolutionFunctorOne

-- Proof sketch: for each morphism of bounded-below complexes, Lemmas 13.18.6 and 13.18.7 give a
-- unique induced morphism between the chosen injective resolutions in the homotopy category.
-- Those unique lifts force preservation of identities and composition, so the objectwise
-- resolution data extends uniquely to the canonical homotopy-category owner
-- `CategoryTheory.HomotopyResolutionFunctor`.
/-- Lemma 13.23.3: a resolution functor 1 on bounded-below cochain complexes admits a unique
homotopy-category realization. Equivalently, there is a unique
`HomotopyResolutionFunctor 𝒜` equipped with the canonical objectwise isomorphisms whose
comparison morphisms agree in `K^+(\mathcal A)` with the chosen quasi-isomorphisms of `R`. -/
theorem existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne
    (R : ResolutionFunctorOne 𝒜) :
    ∃! j : HomotopyResolutionFunctor 𝒜, R.RealizedBy j := sorry

end CochainComplex

/-! ### Lemma_13_23_4 (from Chap13) -/
open CategoryTheory
open CochainComplex

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: bounded-below injective resolutions in the homotopy category and their
  functorial uniqueness;
- sampled owner declarations:
  `CochainComplex.ResolutionFunctorOne`,
  `CochainComplex.ResolutionFunctorOne.RealizedBy`,
  `CochainComplex.existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne`,
  `CategoryTheory.HomotopyResolutionFunctor`;
- best owner abstraction: the primitive source-facing data is
  `CochainComplex.ResolutionFunctorOne 𝒜`, while
  `CategoryTheory.HomotopyResolutionFunctor 𝒜` is the canonical homotopy-category owner obtained
  from it by the bridge theorem `existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne`;
- primitive data: an objectwise choice of bounded-below injective resolutions of complexes;
- derived API: existence of a homotopy resolution functor and the unique compatible natural
  isomorphism between two such functors.

Source/core/bridge triage:
- `source-facing`: existence of a resolution functor 1 and the comparison isomorphism between two
  resulting homotopy resolution functors;
- `core/canonical`: `CategoryTheory.HomotopyResolutionFunctor 𝒜`;
- `bridge/view`: the realization theorem
  `CochainComplex.existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne`.
-/

-- Proof sketch: for each bounded-below complex `K`, Lemma 13.18.3 provides an injective
-- resolution of `K.obj`; collecting these choices gives the primitive source-facing data of a
-- resolution functor 1.
/-- If an abelian category has enough injectives, then bounded-below cochain complexes admit a
resolution functor 1 in the sense of Definition 13.23.2. -/
theorem exists_resolutionFunctorOne [EnoughInjectives 𝒜] :
    Nonempty (ResolutionFunctorOne 𝒜) := by
  classical
  refine ⟨fun K ↦ ?_⟩
  let hplus : ∃ a : ℤ, K.obj.IsStrictlyGE a := (CochainComplex.plus_iff 𝒜 K.obj).mp K.property
  let a : ℤ := Classical.choose hplus
  let hK : K.obj.IsStrictlyGE a := Classical.choose_spec hplus
  exact Classical.choice <|
    nonempty_injectiveResolution_of_eventually_isZero_homology <|
      ⟨a, fun n hn ↦ by
        let _ : K.obj.IsStrictlyGE a := hK
        simpa using K.obj.isZero_of_isGE a n hn⟩

-- Proof sketch: first choose a resolution functor 1 using `exists_resolutionFunctorOne`, then
-- apply the bridge theorem
-- `CochainComplex.existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne` to realize it
-- uniquely in the homotopy category.
/-- Lemma 13.23.4 (1): if an abelian category has enough injectives, then bounded-below cochain
complexes admit a homotopy resolution functor. -/
theorem exists_homotopyResolutionFunctor [EnoughInjectives 𝒜] :
    Nonempty (HomotopyResolutionFunctor 𝒜) := by
  obtain ⟨R⟩ : Nonempty (ResolutionFunctorOne 𝒜) := exists_resolutionFunctorOne
  obtain ⟨J, -, -⟩ := existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne R
  exact ⟨J⟩

local notation "KinjIncl" => ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)

-- Proof sketch: for two homotopy resolution functors, compare their underlying objectwise choices
-- of injective resolutions. The objectwise comparison maps are uniquely determined by the
-- compatibility with the quasi-isomorphisms from `K`, and these unique componentwise maps
-- assemble into a unique natural isomorphism.
/-- Any comparison natural isomorphism between two homotopy resolution functors compatible with
the canonical quasi-isomorphisms exists and is unique. -/
theorem existsUnique_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    ∃! e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := sorry

/-- Lemma 13.23.4 (2): any two homotopy resolution functors are isomorphic by a natural
isomorphism compatible with the comparison quasi-isomorphisms. -/
theorem exists_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    ∃ e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := by
  obtain ⟨e, he, -⟩ := existsUnique_homotopyResolutionFunctorIso J J'
  exact ⟨e, he⟩

-- Proof sketch: the compatibility with the comparison quasi-isomorphisms makes the component on
-- each bounded-below complex the unique comparison map between two injective resolutions, so this
-- is the `Subsingleton` consequence of
-- `existsUnique_homotopyResolutionFunctorIso`; the enough-injectives hypothesis is redundant once the
-- two homotopy resolution functors are already given.
/-- Lemma 13.23.4 (3): the comparison natural isomorphism between two homotopy resolution
functors is unique. -/
theorem subsingleton_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    Subsingleton
      { e : J.toFunctor ≅ J'.toFunctor //
          J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι } := by
  refine ⟨fun a b ↦ ?_⟩
  obtain ⟨e, _, huniq⟩ := existsUnique_homotopyResolutionFunctorIso J J'
  apply Subtype.ext
  calc
    a.1 = e := huniq a.1 a.2
    _ = b.1 := (huniq b.1 b.2).symm

end CategoryTheory

/-! ### Lemma_13_23_5 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling for Lemma 13.23.5:
- primary domain: bounded-below injective complexes in the homotopy category and exact functors
  between triangulated categories;
- sampled owner declarations:
  `CochainComplex.InjectivePlus`,
  `CochainComplex.InjectivePlus.toHomotopy`,
  `Functor.CommShift`,
  `Functor.IsTriangulated`;
- best owner abstraction: the source-facing owners in this file are the full subcategory
  `K^+(\mathcal I) ⊆ K^+(\mathcal A)` and the corresponding homotopy resolution functor, while
  exactness itself is owned canonically upstream by `Functor.CommShift` together with
  `Functor.IsTriangulated`;
- primitive-vs-derived split:
  primitive data: the chapter owner `CochainComplex.InjectivePlus 𝒜`, its homotopy-category image,
    a functor into that full subcategory, and the comparison natural transformation from the
    identity;
  derived API: the triangulated instance on the injective subcategory and the exactness statement
    for the chosen resolution functor.

Source/core/bridge triage:
- `source-facing`: `HomotopyResolutionFunctor`;
- `core/canonical`: `CochainComplex.InjectivePlus` for the complex-level injective owner and the
  exact-functor owners `Functor.CommShift` and `Functor.IsTriangulated`;
- `bridge/view`: `boundedBelowInjectiveHomotopyProperty`, `boundedBelowInjectiveHomotopyCat`, and
  `CochainComplex.InjectivePlus.toHomotopy`, which pass from bounded-below injective complexes to
  their homotopy-category image before expressing exactness in the canonical triangulated API.
-/

/-- The object property on `K^+(\mathcal A)` cutting out the bounded-below complexes whose terms
are injective objects of `𝒜`, read via the chapter owner `CochainComplex.InjectivePlus 𝒜`. -/
abbrev boundedBelowInjectiveHomotopyProperty (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :
    ObjectProperty (K⁺(𝒜)) :=
  fun K ↦
    let C : CochainComplex 𝒜 ℤ := K.obj.as
    ∀ n : ℤ, Injective (C.X n)

/-- The bounded-below homotopy category `K^+(\mathcal I)` of complexes of injective objects in
`𝒜`. -/
abbrev boundedBelowInjectiveHomotopyCat (𝒜 : Type u)
    [Category.{v} 𝒜] [Abelian 𝒜] :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).FullSubcategory

/- The textbook category `K^+(\mathcal I)` depends on the ambient abelian category `𝒜` through
its injective objects. The scoped notation `K⁺ᵢ(𝒜)` keeps that ambient parameter explicit on the
Lean theorem surface while replacing the raw owner name. -/
scoped[CategoryTheory] notation:max "K⁺" "ᵢ(" A:arg ")" => boundedBelowInjectiveHomotopyCat A

namespace CochainComplex.InjectivePlus

/-- The quotient bridge from bounded-below complexes of injectives to their image
`K^+(\mathcal I) ⊆ K^+(\mathcal A)`. -/
abbrev toHomotopy (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :
    CochainComplex.InjectivePlus 𝒜 ⥤ K⁺ᵢ(𝒜) :=
  (boundedBelowInjectiveHomotopyProperty 𝒜).lift
    (ObjectProperty.ι
      (fun K : CochainComplex.Plus 𝒜 ↦ ∀ n : ℤ, Injective (K.obj.X n)) ⋙
        HomotopyCategory.Plus.quotient 𝒜)
    (fun I n ↦ by simpa using I.term_mem n)

end CochainComplex.InjectivePlus

namespace boundedBelowInjectiveHomotopyCat

/-- An object of `K^+(\mathcal I)` determines its underlying bounded-below cochain complex of
injective objects. -/
abbrev toInjectivePlus (I : K⁺ᵢ(𝒜)) : CochainComplex.InjectivePlus 𝒜 :=
  let K : K⁺(𝒜) := I.obj
  ⟨⟨K.obj.as, K.property⟩, fun n ↦ by
    simpa using I.property n⟩

end boundedBelowInjectiveHomotopyCat

-- Proof sketch: the shift of a bounded-below complex of injectives is again termwise injective,
-- and the cone of a morphism between such complexes has terms built from finite biproducts of
-- injectives, so it stays inside the same triangulated object property.
/-- The bounded-below injective object property on `K^+(\mathcal A)` is triangulated. -/
instance boundedBelowInjectiveHomotopyProperty_isTriangulated :
    ObjectProperty.IsTriangulated (boundedBelowInjectiveHomotopyProperty 𝒜) := sorry

/-- A resolution functor on `K^+(\mathcal A)` is a functor from the bounded-below homotopy
category to the full triangulated subcategory of bounded-below complexes of injectives, together
with a natural quasi-isomorphism from the identity functor after forgetting injectivity. -/
structure HomotopyResolutionFunctor (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] where
  /-- The underlying functor `K^+(\mathcal A) ⥤ K^+(\mathcal I)`. -/
  toFunctor : K⁺(𝒜) ⥤ K⁺ᵢ(𝒜)
  /-- The comparison morphism from a bounded-below complex to its chosen injective resolution. -/
  ι : 𝟭 (K⁺(𝒜)) ⟶
    toFunctor ⋙ ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)
  /-- The comparison morphism is a quasi-isomorphism in `K^+(\mathcal A)` on every object. -/
  quasiIso_app (K : K⁺(𝒜)) : Qis⁺(𝒜) (ι.app K)

namespace HomotopyResolutionFunctor

-- Proof sketch: for each `n : ℤ`, compare the two injective resolutions `j(K⟦n⟧)` and
-- `j(K)⟦n⟧` of the shifted object `K⟦n⟧`. Lemmas 13.18.6 and 13.18.7 give a unique comparison
-- isomorphism compatible with the quasi-isomorphisms from `K⟦n⟧`, and these isomorphisms assemble
-- functorially into a `CommShift ℤ` structure. For a distinguished triangle
-- `(K, L, M, f, g, h)`, the comparison quasi-isomorphisms identify the image triangle
-- `(j(K), j(L), j(M), j(f), j(g), ξ_K ≫ j(h))` with a distinguished triangle in `D^+(\mathcal A)`;
-- Proposition 13.23.1 and Lemma 13.4.18 then imply that it is distinguished already in
-- `K^+(\mathcal I)`.
/-- Lemma 13.23.5: any resolution functor
`j : K^+(\mathcal A) ⥤ K^+(\mathcal I)` is exact, i.e. admits a shift-commuting structure for
which it is triangulated. -/
theorem toFunctor_exact (j : HomotopyResolutionFunctor 𝒜) :
    ∃ hcomm : j.toFunctor.CommShift ℤ,
      letI : j.toFunctor.CommShift ℤ := hcomm
      j.toFunctor.IsTriangulated := sorry

end HomotopyResolutionFunctor

end CategoryTheory

/-! ### Lemma_13_23_6 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Localization
open CategoryTheory.ObjectProperty
open CochainComplex
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe v u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "Q" => (mapBoundedBelowHomotopyToDerivedBelow : K⁺(𝒜) ⥤ D⁺(𝒜))
local notation "KinjIncl" =>
  (ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜))
local notation "IToD" => KinjIncl ⋙ Q

/- Domain-style sampling for Lemma 13.23.6:
- primary domain: localization of the bounded-below homotopy category at quasi-isomorphisms and
  the comparison with bounded-below complexes of injectives;
- sampled owner declarations:
  `Functor.IsLocalization`,
  `Localization.lift`,
  `Localization.fac`,
  `Localization.liftNatIso`,
  `ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜) ⋙
  mapBoundedBelowHomotopyToDerivedBelow`;
- best owner abstraction: the core/canonical factorization of a resolution functor through
  `D^+(\mathcal A)` is owned by `Localization.lift` for the localization functor
  `Q : K^+(\mathcal A) ⥤ D^+(\mathcal A)`, while the source-facing uniqueness statement should be
  expressed through the canonical lifting isomorphism API rather than by strict functor equality;
- primitive data: the functor `j.toFunctor : K^+(\mathcal A) ⥤ K^+(\mathcal I)` and the fact
  that it inverts bounded-below quasi-isomorphisms;
- derived API: the factorization through `D^+(\mathcal A)` and the resulting quasi-inverse
  equivalence statement for that factorization.

Source/core/bridge triage:
- `source-facing`: the canonical factorization of a homotopy resolution functor through
  `D^+(\mathcal A)` and its uniqueness up to unique isomorphism;
- `core/canonical`: `Localization.lift`, `Localization.fac`, `Localization.liftNatIso`, and
  `Functor.IsLocalization Q (Qis⁺(𝒜))`;
- `bridge/view`: the quasi-inverse natural isomorphisms obtained by combining the canonical lift
  with the bounded-below injective Hom-to-derived bijection.
-/
attribute [local instance] mapBoundedBelowHomotopyToDerivedBelow_isLocalization

namespace HomotopyResolutionFunctor

-- Proof sketch: if `j' : D^+(\mathcal A) ⥤ K^+(\mathcal I)` is any other factorization equipped
-- with an isomorphism `Q ⋙ j' ≅ j.toFunctor`, then both `j'` and `Localization.lift ...` are
-- liftings of the same functor out of `K^+(\mathcal A)`. The existence part is owned canonically
-- by `Localization.fac`, and uniqueness is obtained by applying `Localization.liftNatIso` to the
-- identity isomorphism of `j.toFunctor`.
/-- Lemma 13.23.6, uniqueness companion: any two factorizations of `j.toFunctor` through
`D^+(\mathcal A)` are canonically isomorphic once their comparison with `Q` is specified. -/
noncomputable def lift_unique (j : HomotopyResolutionFunctor 𝒜)
    (j' : D⁺(𝒜) ⥤ K⁺ᵢ(𝒜)) (e : Q ⋙ j' ≅ j.toFunctor) :
    j' ≅ j.lift := by
  letI : Localization.Lifting Q (Qis⁺(𝒜)) j.toFunctor j' := ⟨e⟩
  exact
    Localization.liftNatIso Q (Qis⁺(𝒜)) j.toFunctor j.toFunctor j'
      j.lift (Iso.refl _)

/-- Lemma 13.23.6: the canonical localization lift of a homotopy resolution functor is an
equivalence of categories, with quasi-inverse the canonical functor
`K^+(\mathcal I) ⥤ D^+(\mathcal A)`. -/
theorem lift_isEquivalence (j : HomotopyResolutionFunctor 𝒜) :
    Functor.IsEquivalence j.lift := by
  let _ : Functor.IsEquivalence IToD := by
    simpa using j.toDerived_isEquivalence
  let _ : Functor.IsEquivalence (j.lift ⋙ IToD) :=
    Functor.isEquivalence_of_iso j.lift_unitIso
  exact Functor.isEquivalence_of_comp_right j.lift IToD

end HomotopyResolutionFunctor

end

end CategoryTheory

/-! ### Remark_13_23_7 (from Chap13) -/
open CategoryTheory ComplexShape HomotopyCategory

noncomputable section

universe v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/- Domain-style sampling:
- primary domain: canonical comparison morphisms between injective resolutions of the same
  cochain complex in the homotopy category;
- sampled owner declarations:
  `CochainComplex.InjectiveResolution`,
  `CochainComplex.InjectiveResolution.injective`,
  `CochainComplex.InjectiveResolution.plus`,
  `CochainComplex.homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`;
- best owner abstraction: the source-facing owner here is
  `CochainComplex.InjectiveResolution`, while the precomposition bijection of Remark 13.18.5 is
  the core/canonical theorem controlling comparison morphisms into a bounded-below injective
  complex;
- primitive data: a cochain complex `K` together with injective resolutions `I`, `J` of `K`;
- derived API: the canonical homotopy-category comparison morphism `I ⟶ J` and the
  source-facing uniqueness statement that characterizes it.

Source/core/bridge triage:
- `source-facing`: the `InjectiveResolution` comparison morphism and its uniqueness statement;
- `core/canonical`: `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective`;
- `bridge/view`: none; this file should use the core bijection directly rather than introducing a
  parallel local comparison-morphism API outside the injective-resolution owner namespace.
-/

namespace InjectiveResolution

private noncomputable def comparisonEquiv {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    ((quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J) ≃
      ((quotient 𝒜 (up ℤ)).obj K ⟶ (quotient 𝒜 (up ℤ)).obj J) :=
  let Q := quotient 𝒜 (up ℤ)
  Equiv.ofBijective (fun a : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ a)
    (homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective I.ι J)

-- Proof sketch: apply the core owner theorem
-- `homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective` to the
-- quasi-isomorphism `I.ι : K ⟶ I`. The desired morphism is the unique preimage of the class of
-- `J.ι` under the resulting bijection.
/-- The canonical comparison morphism between two injective resolutions of the same cochain
complex in the homotopy category. -/
noncomputable def homotopyComparison {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J :=
  (comparisonEquiv I J).symm ((quotient 𝒜 (up ℤ)).map J.ι)

@[reassoc]
theorem ι_homotopyComparison {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    (quotient 𝒜 (up ℤ)).map I.ι ≫ homotopyComparison I J =
      (quotient 𝒜 (up ℤ)).map J.ι := by
  let Q := quotient 𝒜 (up ℤ)
  let e := comparisonEquiv I J
  change (fun a : Q.obj I ⟶ Q.obj J ↦ Q.map I.ι ≫ a) (e.symm (Q.map J.ι)) = Q.map J.ι
  exact e.apply_symm_apply (Q.map J.ι)

attribute [simp] ι_homotopyComparison_assoc

  theorem homotopyComparison_unique {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K)
    {a : (quotient 𝒜 (up ℤ)).obj I ⟶ (quotient 𝒜 (up ℤ)).obj J}
    (ha : (quotient 𝒜 (up ℤ)).map I.ι ≫ a = (quotient 𝒜 (up ℤ)).map J.ι) :
    a = homotopyComparison I J := by
  let hbij :=
    homotopyCategory_precomp_bijective_of_quasiIso_to_boundedBelow_injective I.ι J
  exact hbij.injective (ha.trans (I.ι_homotopyComparison J).symm)

/-- Remark 13.23.7: for injective resolutions `I` and `J` of a cochain complex `K`, there is a
unique morphism from `I` to `J` in the homotopy category whose composite with the map `K ⟶ I` is
the map `K ⟶ J`. The source text assumes `K` bounded below, but that hypothesis is redundant once
`I` and `J` are given. -/
theorem existsUnique_homotopyComparison
    {K : CochainComplex 𝒜 ℤ} (I J : InjectiveResolution K) :
    ∃! a :
        (quotient 𝒜 (up ℤ)).obj I ⟶
          (quotient 𝒜 (up ℤ)).obj J,
      (quotient 𝒜 (up ℤ)).map I.ι ≫ a =
        (quotient 𝒜 (up ℤ)).map J.ι := by
  refine ⟨homotopyComparison I J, I.ι_homotopyComparison J, ?_⟩
  intro a ha
  exact homotopyComparison_unique I J ha

end InjectiveResolution

end CochainComplex
