import Mathlib
import StacksProject_2024.Chap10.Lemma_10_147_5
import StacksProject_2024.Chap16.Lemma_16_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- Helper for Chap16 Lemma 16 3 5: a standard smooth `CommRingCat` arrow is finitely
presentable for the categorical owner used by `MorphismProperty.ind`. -/
lemma commRingCatIsFinitelyPresentableHom_of_standardSmooth
    {X Y : CommRingCat} (f : X ⟶ Y)
    (hf : (RingHom.toMorphismProperty RingHom.IsStandardSmooth) f) :
    CategoryTheory.MorphismProperty.isFinitelyPresentable CommRingCat f := by
  -- Proof comment: standard smooth ring maps are smooth, hence finitely presented, and
  -- `CommRingCat` already packages finitely presented ring maps as finitely presentable arrows.
  exact CommRingCat.isFinitelyPresentable_hom f hf.smooth.finitePresentation

/-- Helper for Chap16 Lemma 16 3 5: a smooth `CommRingCat` arrow is finitely presentable for the
categorical owner used by `MorphismProperty.ind`. -/
lemma commRingCatIsFinitelyPresentableHom_of_smooth
    {X Y : CommRingCat} (f : X ⟶ Y)
    (hf : (RingHom.toMorphismProperty RingHom.Smooth) f) :
    CategoryTheory.MorphismProperty.isFinitelyPresentable CommRingCat f := by
  -- Proof comment: smooth ring maps are finitely presented, and `CommRingCat` already packages
  -- finitely presented ring maps as finitely presentable arrows.
  exact CommRingCat.isFinitelyPresentable_hom f hf.finitePresentation

/-- Helper for Chap16 Lemma 16 3 5: replacing a smooth stage `B` by a retract stage `C`
preserves the resulting factorization to the target. -/
lemma smoothStageToRetractStageFactorization
    {Z B C A : Type*} [CommRing Z] [CommRing B] [CommRing C] [CommRing A]
    [Algebra B C] (u : CommRingCat.of Z ⟶ CommRingCat.of B)
    (v : CommRingCat.of B ⟶ CommRingCat.of A) (g : CommRingCat.of Z ⟶ CommRingCat.of A)
    (r : C →ₐ[B] B) (huv : u ≫ v = g) :
    CommRingCat.ofHom ((algebraMap B C).comp u.hom) ≫
        CommRingCat.ofHom (v.hom.comp r.toRingHom) =
      g := by
  -- Proof comment: evaluate the refined composite at each element of `Z`, then collapse the
  -- inserted `B`-algebra retraction by `r.commutes`.
  apply CommRingCat.hom_ext_iff.mpr
  intro z
  have huvz := congrArg (fun ψ : CommRingCat.of Z ⟶ CommRingCat.of A => ψ.hom z) huv
  change v.hom (r.toRingHom ((algebraMap B C) (u.hom z))) = g.hom z
  simpa [RingHom.comp_apply] using huvz

/-- Helper for Chap16 Lemma 16 3 5: after refining the smooth stage `B` to a retract stage `C`,
the induced source map is the algebra map `R → C` coming from the scalar tower. -/
lemma retractStageSource_eq_algebraMap
    {R Z B C : Type*} [CommRing R] [CommRing Z] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]
    (p : CommRingCat.of R ⟶ CommRingCat.of Z)
    (u : CommRingCat.of Z ⟶ CommRingCat.of B)
    (hpu : p ≫ u = CommRingCat.ofHom (algebraMap R B)) :
    p ≫ CommRingCat.ofHom ((algebraMap B C).comp u.hom) =
      CommRingCat.ofHom (algebraMap R C) := by
  -- Proof comment: compose the original source-compatibility equation with `algebraMap B C`,
  -- then rewrite the resulting tower composite as `algebraMap R C`.
  apply CommRingCat.hom_ext_iff.mpr
  intro x
  have hpux := CommRingCat.hom_ext_iff.mp hpu x
  change u.hom (p.hom x) = algebraMap R B x at hpux
  change (algebraMap B C) (u.hom (p.hom x)) = algebraMap R C x
  simpa [RingHom.comp_apply, IsScalarTower.algebraMap_eq R B C] using
    congrArg (fun b : B => (algebraMap B C) b) hpux

/-- Helper for Chap16 Lemma 16 3 5: a standard smooth `R`-algebra gives the corresponding
categorical morphism-property witness on its algebra map. -/
lemma standardSmoothMorphismProperty_of_algebra
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (hstd : Algebra.IsStandardSmooth R A) :
    (RingHom.toMorphismProperty RingHom.IsStandardSmooth)
      (CommRingCat.ofHom (algebraMap R A)) := by
  -- Proof comment: `RingHom.isStandardSmooth_algebraMap` is the canonical bridge from the
  -- algebra-level owner to the ring-hom owner used by `MorphismProperty.ind`.
  exact RingHom.isStandardSmooth_algebraMap.mpr hstd

/-- Helper for Chap16 Lemma 16 3 5: a smooth ring map equips its codomain with the corresponding
`Smooth` algebra instance coming from `toAlgebra`. -/
lemma smooth_toAlgebra_of_smooth
    {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) (hf : f.Smooth) :
    @Smooth R A _ _ f.toAlgebra := by
  -- Proof comment: `RingHom.smooth_algebraMap` identifies smoothness of the algebra map attached
  -- to `f` with the `Smooth` typeclass on the induced `R`-algebra structure.
  simpa [RingHom.smooth_algebraMap, RingHom.algebraMap_toAlgebra] using hf

/- Domain-style sampling for Lemma 16.3.5:
* primary domain: filtered colimits of smooth and standard smooth commutative ring maps;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth`, the Chapter 10 source-facing owner for PT
    presentations;
  - `RingHom.IsFilteredColimitOfEtale`, the analogous source-facing owner hiding the same-universe
    `ULift` bookkeeping for a filtered-colimit morphism property;
  - `RingHom.IsFilteredColimitOfWeaklyEtale`, the later chapter-level repetition of the same
    source-facing wrapper pattern for a different morphism property;
  - `CategoryTheory.MorphismProperty.ind`, the generic owner for filtered-colimit closure of a
    morphism property;
  - `RingHom.IsStandardSmooth`, the canonical owner for standard smoothness of a ring map.
* best owner abstraction: `RingHom.IsFilteredColimitOfStandardSmooth`, with hidden core/canonical
  content `ind (toMorphismProperty RingHom.IsStandardSmooth)`;
* primitive data: only the ring map `f : R →+* A`;
* derived API: any chosen filtered diagram, cocone, and comparison isomorphism witnessing the
  filtered-colimit presentation.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsFilteredColimitOfStandardSmooth`;
* `core/canonical`: `ind (toMorphismProperty RingHom.IsStandardSmooth)`;
* `bridge/view`: the hidden same-universe `ULift` presentation of `f` used to speak to
  `CategoryTheory.MorphismProperty.ind`.

The review correction for this file is that the theorem should not expose the raw
`CommRingCat`-level owner `(toMorphismProperty RingHom.IsStandardSmooth).ind (ofHom ...)`.
Parallel to `RingHom.IsFilteredColimitOfSmooth`, `...Etale`, and `...WeaklyEtale`, the
source-facing owner here should be a ring-hom property hiding the `ULift` bookkeeping.
-/

/-- An `R`-algebra map `f : R →+* A` is a filtered colimit of standard smooth `R`-algebras. This
thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the
canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty RingHom.IsStandardSmooth)`. -/
abbrev IsFilteredColimitOfStandardSmooth (f : R →+* A) : Prop :=
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift A) := ULift.algebra' R (ULift A)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty IsStandardSmooth)
    (ofHom (algebraMap (ULift.{v} R) (ULift A)))

-- Proof sketch: use Lemma `10.127.4` in the standard-smooth variant. Given a finitely presented
-- `R`-algebra mapping to `A`, factor the map through one of the smooth stages of the given
-- filtered colimit presentation, then apply Lemma `16.3.4` to replace that smooth stage by a
-- standard smooth `R`-algebra through which the map still factors.
/-- Lemma 16.3.5: if a ring map `R → A` is a filtered colimit of smooth `R`-algebras, then it is
a filtered colimit of standard smooth `R`-algebras. -/
@[stacks 07CI]
theorem isFilteredColimitOfStandardSmooth_of_isFilteredColimitOfSmooth
    {f : R →+* A} (h : f.IsFilteredColimitOfSmooth) :
    f.IsFilteredColimitOfStandardSmooth := by
  let _ : Algebra R A := f.toAlgebra
  let _ : Algebra R (ULift A) := ULift.algebra
  let _ : Algebra (ULift R) (ULift A) := ULift.algebra' R (ULift A)
  -- Route correction: unfold the owner once and prove the standard-smooth wrapper directly with
  -- `MorphismProperty.ind_iff_exists`, refining one extracted smooth stage via Lemma `16.3.4`.
  dsimp [RingHom.IsFilteredColimitOfStandardSmooth]
  have hcolim :
      CategoryTheory.MorphismProperty.ind
        (RingHom.toMorphismProperty RingHom.Smooth)
        (CommRingCat.ofHom (algebraMap (ULift R) (ULift A))) := by
    -- Proof comment: the source-facing smooth wrapper is exactly the hidden lifted `ind` witness.
    simpa [RingHom.IsFilteredColimitOfSmooth] using h
  refine
    (CategoryTheory.MorphismProperty.ind_iff_exists
      (C := CommRingCat)
      (P := RingHom.toMorphismProperty RingHom.IsStandardSmooth)
      (H := commRingCatIsFinitelyPresentableHom_of_standardSmooth)
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift A)))).2 ?_
  intro Z p g hp hpg
  obtain ⟨B, u, v, huv, hSmoothStage⟩ :=
    ((CategoryTheory.MorphismProperty.ind_iff_exists
      (C := CommRingCat)
      (P := RingHom.toMorphismProperty RingHom.Smooth)
      (H := commRingCatIsFinitelyPresentableHom_of_smooth)
      (CommRingCat.ofHom (algebraMap (ULift R) (ULift A)))).1 hcolim) p g hp hpg
  let sourceToB : ULift R →+* B := (p ≫ u).hom
  let _ : Algebra (ULift R) B := sourceToB.toAlgebra
  have hpu : p ≫ u = CommRingCat.ofHom (algebraMap (ULift R) B) := by
    -- Proof comment: the extracted stage map defines the `ULift R`-algebra structure on `B`.
    apply CommRingCat.hom_ext_iff.mpr
    intro x
    rfl
  have hsourceSmooth : sourceToB.Smooth := by
    -- Proof comment: the stage extracted from the smooth filtered-colimit criterion is smooth over
    -- `ULift R`.
    simpa [hpu, sourceToB, RingHom.toMorphismProperty] using hSmoothStage
  let _ : Smooth (ULift R) B := smooth_toAlgebra_of_smooth sourceToB hsourceSmooth
  obtain ⟨C, _hC, _hRC, _hBC, _hTower, _hSmoothBC, r, hstdC⟩ :=
    Algebra.exists_smooth_retraction_standardSmooth_of_smooth (R := ULift R) (A := B)
  let u' : Z ⟶ CommRingCat.of C :=
    CommRingCat.ofHom ((algebraMap B C).comp u.hom)
  let v' : CommRingCat.of C ⟶ CommRingCat.of (ULift A) :=
    CommRingCat.ofHom (v.hom.comp r.toRingHom)
  refine ⟨CommRingCat.of C, u', v', ?_, ?_⟩
  · -- Proof comment: the new target map is the old one precomposed with the retraction, so the
    -- factorization to `ULift A` is unchanged.
    simpa [u', v'] using
      smoothStageToRetractStageFactorization (u := u) (v := v) (g := g) r huv
  · -- Proof comment: the retract stage is standard smooth over `ULift R`, and the induced source
    -- map `ULift R → C` is the composite of the old stage map with `B → C`.
    have hpu' :
        p ≫ u' = CommRingCat.ofHom (algebraMap (ULift R) C) :=
      retractStageSource_eq_algebraMap (p := p) (u := u) hpu
    have hstdHom :
        (RingHom.toMorphismProperty RingHom.IsStandardSmooth)
          (CommRingCat.ofHom (algebraMap (ULift R) C)) :=
      standardSmoothMorphismProperty_of_algebra (R := ULift R) hstdC
    simpa [hpu'] using hstdHom

end

end RingHom
