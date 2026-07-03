import Mathlib
import stacks_project.Chap13.Lemma_13_18_3
import stacks_project.Chap13.Lemma_13_23_3

-- Declarations for this item will be appended below by the statement pipeline.

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
