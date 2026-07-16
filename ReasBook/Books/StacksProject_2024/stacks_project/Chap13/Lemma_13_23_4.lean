import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_23_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_18_8
import StacksProject_2024.stacks_project.Chap13.Lemma_13_23_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Localization
open CochainComplex
open DerivedCategory.TStructure

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

attribute [local instance] HasDerivedCategory.standard

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
-- Route correction: the owner API for `HomotopyResolutionFunctor` and `K⁺ᵢ(𝒜)` is imported
-- directly from `Definition_13_23_2`, so validating this uniqueness proof no longer depends on
-- the later exactness file `Lemma_13_23_5`.
/-- Lemma 13.23.4 (1): if an abelian category has enough injectives, then bounded-below cochain
complexes admit a homotopy resolution functor. -/
theorem exists_homotopyResolutionFunctor [EnoughInjectives 𝒜] :
    Nonempty (HomotopyResolutionFunctor 𝒜) := by
  obtain ⟨R⟩ : Nonempty (ResolutionFunctorOne 𝒜) := exists_resolutionFunctorOne
  obtain ⟨J, -, -⟩ := existsUnique_homotopyResolutionFunctor_of_resolutionFunctorOne R
  exact ⟨J⟩

private abbrev KinjIncl : K⁺ᵢ(𝒜) ⥤ K⁺(𝒜) :=
  ObjectProperty.ι (boundedBelowInjectiveHomotopyProperty 𝒜)

private abbrev KplusIncl : K⁺(𝒜) ⥤ K(𝒜) :=
  ObjectProperty.ι (HomotopyCategory.plus 𝒜)

private noncomputable abbrev Qplus : K⁺(𝒜) ⥤ DerivedCategory 𝒜 :=
  KplusIncl ⋙ DerivedCategory.Qh

/-- Helper for Lemma 13.23.4: the comparison morphism of a homotopy resolution functor is a
quasi-isomorphism after forgetting from `K^+(\mathcal A)` to `K(\mathcal A)`. -/
private theorem homotopyResolutionFunctor_quasiIso_ambient
    (J : HomotopyResolutionFunctor 𝒜) (X : K⁺(𝒜)) :
    HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ) (KplusIncl.map (J.ι.app X)) := by
  sorry

/-- Helper for Lemma 13.23.4: morphisms from a bounded-below homotopy object to a bounded-below
injective target are detected uniquely in the ambient derived category. -/
private theorem boundedBelowHomotopyToDerived_map_bijective
    (X : K⁺(𝒜)) (Y : K⁺ᵢ(𝒜)) :
    Function.Bijective
      (Qplus.map : (X ⟶ KinjIncl.obj Y) →
        (Qplus.obj X ⟶ Qplus.obj (KinjIncl.obj Y))) := by
  sorry

/-- Helper for Lemma 13.23.4: a map from `X` into an injective target `Y` factors uniquely through
the canonical resolution morphism `X ⟶ J(X)`. -/
private theorem existsUnique_homotopyResolutionFunctor_lift
    (J : HomotopyResolutionFunctor 𝒜) (X : K⁺(𝒜)) (Y : K⁺ᵢ(𝒜))
    (s : X ⟶ KinjIncl.obj Y) :
    ∃! a : J.toFunctor.obj X ⟶ Y, J.ι.app X ≫ KinjIncl.map a = s := by
  sorry

/-- Helper for Lemma 13.23.4: for a fixed bounded-below complex, two injective resolutions admit a
unique comparison morphism. -/
private theorem existsUnique_homotopyResolutionFunctor_component
    (J J' : HomotopyResolutionFunctor 𝒜) (X : K⁺(𝒜)) :
    ∃! a : J.toFunctor.obj X ⟶ J'.toFunctor.obj X,
      J.ι.app X ≫ KinjIncl.map a = J'.ι.app X := by
  sorry

/-- Helper for Lemma 13.23.4: compatibility with the canonical quasi-isomorphisms forces the
comparison morphisms to be natural. -/
private theorem homotopyResolutionFunctor_component_natural
    {J J' : HomotopyResolutionFunctor 𝒜} {X Y : K⁺(𝒜)} (f : X ⟶ Y)
    {aX : J.toFunctor.obj X ⟶ J'.toFunctor.obj X}
    {aY : J.toFunctor.obj Y ⟶ J'.toFunctor.obj Y}
    (haX : J.ι.app X ≫ KinjIncl.map aX = J'.ι.app X)
    (haY : J.ι.app Y ≫ KinjIncl.map aY = J'.ι.app Y) :
    J.toFunctor.map f ≫ aY = aX ≫ J'.toFunctor.map f := by
  sorry

/-- Helper for Lemma 13.23.4: every comparison morphism between two injective resolutions is an
isomorphism. -/
private theorem homotopyResolutionFunctor_component_isIso
    {J J' : HomotopyResolutionFunctor 𝒜} {X : K⁺(𝒜)}
    {a : J.toFunctor.obj X ⟶ J'.toFunctor.obj X}
    (ha : J.ι.app X ≫ KinjIncl.map a = J'.ι.app X) :
    IsIso a := by
  sorry

/-- Helper for Lemma 13.23.4: any natural isomorphism compatible with the canonical resolution
maps induces the corresponding objectwise lifting equation. -/
private theorem homotopyResolutionFunctorIso_component_eq
    {J J' : HomotopyResolutionFunctor 𝒜} (e : J.toFunctor ≅ J'.toFunctor)
    (he : J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι) (X : K⁺(𝒜)) :
    J.ι.app X ≫ KinjIncl.map (e.hom.app X) = J'.ι.app X := by
  sorry

-- Proof sketch: for two homotopy resolution functors, compare their underlying objectwise choices
-- of injective resolutions. The objectwise comparison maps are uniquely determined by the
-- compatibility with the quasi-isomorphisms from `K`, and these unique componentwise maps
-- assemble into a unique natural isomorphism.
/-- Any comparison natural isomorphism between two homotopy resolution functors compatible with
the canonical quasi-isomorphisms exists and is unique. -/
theorem existsUnique_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    ∃! e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := by
  sorry

/-- Lemma 13.23.4 (2): any two homotopy resolution functors are isomorphic by a natural
isomorphism compatible with the comparison quasi-isomorphisms. -/
theorem exists_homotopyResolutionFunctorIso
    (J J' : HomotopyResolutionFunctor 𝒜) :
    ∃ e : J.toFunctor ≅ J'.toFunctor,
      J.ι ≫ Functor.whiskerRight e.hom KinjIncl = J'.ι := by
  sorry

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
  sorry

end CategoryTheory
