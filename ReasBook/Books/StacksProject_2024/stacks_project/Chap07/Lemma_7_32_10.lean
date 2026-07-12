import Mathlib
import StacksProject_2024.Chap07.Definition_7_32_1
import StacksProject_2024.Chap07.GSetForgetfulPoint
import StacksProject_2024.Chap07.Lemma_7_11_2
import StacksProject_2024.Chap07.Lemma_7_32_7
import StacksProject_2024.Chap07.Lemma_7_32_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe u v w

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 7.32.10:
- primary domain: points of topoi, via the `Type`-valued adjunction
  `p.typeInverseImage ⊣ p.typePushforward`;
- sampled owner declarations:
  `MorphismOfTopoiIn.typePushforward`,
  `MorphismOfTopoiIn.typeAdjunction`,
  `MorphismOfTopoiIn.pointPushforwardFiber_counit_isSplitEpi`,
  `Adjunction.faithful_R_of_epi_counit_app`;
- best owner abstraction: the owner functor `p.typePushforward`, with its adjunction as primitive
  data and its preservation/reflection properties as derived API;
- primitive data: the topos point `p : MorphismOfTopoiIn J typesGrothendieckTopology` and the
  adjunction already packaged in `Definition_7_32_1`;
- derived API: functorial properties of `p.typePushforward`, plus the sheaf-side predicates
  `Sheaf.IsLocallyInjective` and `Sheaf.IsLocallySurjective` as mono/epi bridge language;
- source/core/bridge triage:
  `source-facing`: the numbered clauses of Lemma 7.32.10;
  `core/canonical`: `p.typeAdjunction` and the functor classes on `p.typePushforward`;
  `bridge/view`: `Sheaf.isLocallyInjective_iff_mono` and
    `Sheaf.isLocallySurjective_iff_epi`. -/

-- Proof sketch: `p.pushforward` is the right adjoint in the adjunction `p.inverseImage ⊣
-- p.pushforward`, and right adjoints preserve all limits.
/-- Lemma 7.32.10 (1): for a point `p : Sh(pt) ⟶ Sh(𝒞)` of the topos associated to a site
`(𝒞, J)`, the direct-image functor `p_* : Type w ⥤ Sh(J, Type w)` commutes with arbitrary
limits. -/
theorem toposPoint_pushforward_preservesLimits
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesLimits p.typePushforward := by
  infer_instance

-- Proof sketch: clause (1) gives preservation of all limits, hence in particular of finite
-- limits, which is exactly left exactness.
/-- Lemma 7.32.10 (2): the direct-image functor of a topos point is left exact. -/
theorem toposPoint_pushforward_leftExact
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    PreservesFiniteLimits p.typePushforward := by
  infer_instance

-- Proof sketch: the counit map `p.inverseImage.obj (p.pushforward.obj E) ⟶ E` is canonically a
-- split epimorphism; if two maps `E ⟶ E'` become equal after applying `p.pushforward`, applying
-- `p.inverseImage` and composing with the splitting forces the original maps to agree.
/-- Lemma 7.32.10 (3): the direct-image functor of a topos point is faithful. -/
theorem toposPoint_pushforward_faithful
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.Faithful := by
  letI (E : Type w) : Epi ((p.typeAdjunction.counit).app E) := by
    letI := MorphismOfTopoiIn.pointPushforwardFiber_counit_isSplitEpi p E
    infer_instance
  exact p.typeAdjunction.faithful_R_of_epi_counit_app

-- Proof sketch: after identifying the point with a site point as in Lemma `7.32.7`, the sheaf
-- `p_* E` is given by `U ↦ (u(U) → E)`, and postcomposition with a surjective map of sets is
-- locally surjective on these section sets.
/-- Lemma 7.32.10 (4): the direct-image functor of a topos point sends surjective maps of sets to
surjective morphisms of sheaves. -/
theorem toposPoint_pushforward_map_surjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Function.Surjective f) :
    Sheaf.IsLocallySurjective (p.typePushforward.map f) := sorry

/- The raw source sentence includes a coequalizer-preservation clause, but Chapter 7 later
produces a concrete group-action counterexample: the point attached to the forgetful functor on
`(Multiplicative (ZMod 2))`-sets has right-translation/coinduction pushforward, and
`Example_7_41_5` shows that this functor does not preserve coequalizers. We therefore keep the
validated clauses above and record the canonical counterexample on the owner `p.typePushforward`
itself instead of a false universal statement. -/
/-- Counterexample to the overstated coequalizer-preservation clause: the direct-image functor of
the canonical point of the surjective site of `(Multiplicative (ZMod 2))`-sets does not commute
with coequalizers. -/
theorem gSetForgetfulPoint_toposPoint_not_preservesCoequalizers :
    ¬ PreservesColimitsOfShape WalkingParallelPair
      (((gSetForgetfulPoint (Multiplicative (ZMod 2))).toToposPoint).typePushforward) := by
  sorry

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, hence it reflects
-- monomorphisms. Translate local injectivity of sheaves to `Mono` using
-- `Sheaf.isLocallyInjective_iff_mono`, reflect along `p.typePushforward`, and read the result
-- back in `Type` via `mono_iff_injective`.
/-- Lemma 7.32.10 (5): if the direct image of a map of sets is injective as a morphism of sheaves,
then the original map is injective. -/
theorem toposPoint_pushforward_reflectsInjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Sheaf.IsLocallyInjective (p.typePushforward.map f)) :
    Function.Injective f := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  exact (mono_iff_injective f).1 <|
    p.typePushforward.mono_of_mono_map <|
      (Sheaf.isLocallyInjective_iff_mono _).1 hf

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, hence it reflects epimorphisms.
-- Local surjectivity of sheaves provides `Epi (p.typePushforward.map f)`, and reflecting this
-- back to `Type` identifies `f` as surjective via `epi_iff_surjective`.
/-- Lemma 7.32.10 (6): if the direct image of a map of sets is surjective as a morphism of
sheaves, then the original map is surjective. -/
theorem toposPoint_pushforward_reflectsSurjective
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) {E E' : Type w} (f : E → E')
    (hf : Sheaf.IsLocallySurjective (p.typePushforward.map f)) :
    Function.Surjective f := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  letI : Epi (p.typePushforward.map f) := by infer_instance
  exact (epi_iff_surjective f).1 <| p.typePushforward.epi_of_epi_map inferInstance

-- Proof sketch: clause (3) makes `p.typePushforward` faithful, and faithful functors reflect
-- monomorphisms and epimorphisms. Since `Type` is balanced, this gives reflection of
-- isomorphisms.
/-- Lemma 7.32.10 (7): the direct-image functor of a topos point reflects isomorphisms. -/
theorem toposPoint_pushforward_reflectsIsomorphisms
    (p : MorphismOfTopoiIn J typesGrothendieckTopology.{w}) :
    p.typePushforward.ReflectsIsomorphisms := by
  letI : p.typePushforward.Faithful := toposPoint_pushforward_faithful p
  infer_instance

end CategoryTheory
