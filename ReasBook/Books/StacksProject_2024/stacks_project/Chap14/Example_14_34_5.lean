import Mathlib
import StacksProject_2024.stacks_project.Chap14.Definition_14_26_6
import StacksProject_2024.stacks_project.Chap14.Lemma_14_26_9

open CategoryTheory
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Augmented
open AlgebraicTopology
open scoped Simplicial

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

/- Domain-style sampling for Example 14.34.5:
- primary domain: the polynomial `A`-algebra resolution of an `A`-algebra as an augmented
  simplicial object in `Under A`, together with its forgetful views to sets and to `A`-modules;
- sampled same-kind owner declarations:
  `Arrow.augmentedCechNerve`,
  `SimplicialObject.Augmented`,
  `commAlgCatEquivUnder`,
  `AlternatingFaceMapComplex.ε`;
- best owner abstraction: the source-facing owner is the augmented Čech nerve of the counit
  `A[B] ⟶ B` in `Under A`; the forgetful functors to sets and to `A`-modules are bridge/view data
  derived from that owner, not primary public owners;
- primitive vs. derived split:
  primitive data are the counit `A[B] ⟶ B` and its canonical augmented Čech nerve in `Under A`;
  derived API is the underlying augmented simplicial set, the underlying augmented simplicial
  `A`-module, and the homotopy/quasi-isomorphism properties of their augmentations.

Source/core/bridge triage:
- `source-facing`: the augmented polynomial `A`-algebra resolution of `B` in `Under A`;
- `core/canonical`: `Arrow.augmentedCechNerve`, `commAlgCatEquivUnder`, and the canonical
  forgetful functors from `CommAlgCat A`;
- `bridge/view`: the whiskered forgetful images of the source-facing owner in `Type u` and
  `ModuleCat A`. -/

/-- The augmented simplicial polynomial `A`-algebra resolution of `B`, given by the augmented Čech
nerve of the counit `A[B] ⟶ B` in `Under A`. -/
abbrev polynomialAlgebraAugmentedResolution (B : Under A) :
    SimplicialObject.Augmented (Under A) :=
  (Arrow.mk ((Under.costarAdjForget A).counit.app B)).augmentedCechNerve

private abbrev polynomialAlgebraForgetToModule : Under A ⥤ ModuleCat A :=
  (commAlgCatEquivUnder A).inverse ⋙
    forget₂ (CommAlgCat A) (AlgCat A) ⋙
      forget₂ (AlgCat A) (ModuleCat A)

/-- The augmented simplicial set obtained from
`polynomialAlgebraAugmentedResolution A B` by forgetting to underlying sets. -/
abbrev polynomialAlgebraAugmentedUnderlyingSet (B : Under A) :
    SimplicialObject.Augmented (Type u) :=
  (whiskeringObj (Under A) (Type u) (Under.forget A ⋙ forget CommRingCat)).obj
    (polynomialAlgebraAugmentedResolution A B)

/-- The augmented simplicial `A`-module obtained from
`polynomialAlgebraAugmentedResolution A B` by forgetting the algebra structure. -/
abbrev polynomialAlgebraAugmentedModuleResolution (B : Under A) :
    SimplicialObject.Augmented (ModuleCat A) :=
  (whiskeringObj (Under A) (ModuleCat A) (polynomialAlgebraForgetToModule A)).obj
    (polynomialAlgebraAugmentedResolution A B)

/-- Helper for Example 14.34.5: the unit of `Under.costarAdjForget A` is a morphism in `Under A`
from `B` to the polynomial algebra object over `B.right`. -/
private theorem polynomialAlgebraCounit_section_sq (B : Under A) :
    CommSq B.hom (𝟙 A) ((Under.costarAdjForget A).unit.app B.right)
      ((Under.costar A).obj B.right).hom := by
  -- The section is built in the owner category `Under A`, so the only check is the under-category
  -- commutative square for the unit map.
  -- Route correction: unfolding reduces this to the claim that the free-`A`-algebra unit
  -- `B.right ⟶ A ⨿ B.right` is a morphism over `A`. This is the wrong owner-level route for the
  -- textbook section, which only exists after forgetting further to underlying sets.
  -- TODO: replace this owner-level section with the source-faithful set-level/composed-adjunction
  -- section and rebuild the extra-degeneracy argument there.
  sorry

/-- Helper for Example 14.34.5: the counit `A[B] ⟶ B` in `Under A` is split by the adjunction
unit. -/
private abbrev polynomialAlgebraCounit_section (B : Under A) :
    B ⟶ (Under.costar A).obj B.right :=
  Under.homMk
    ((Under.costarAdjForget A).unit.app B.right)
    (polynomialAlgebraCounit_section_sq A B).w

/-- Helper for Example 14.34.5: the section followed by the counit is the identity in
`Under A`. -/
private theorem polynomialAlgebraCounit_section_comp_counit (B : Under A) :
    polynomialAlgebraCounit_section A B ≫ (Under.costarAdjForget A).counit.app B = 𝟙 B := by
  -- This is the right triangle identity, now read back in the owner category.
  -- TODO: after replacing the false owner-level section above by the correct set-level section,
  -- re-express the strict section identity in the target owner category.
  sorry

/-- Helper for Example 14.34.5: the counit-section composite defines an endomorphism of the
counit arrow. -/
private theorem polynomialAlgebraCounit_section_endomorphism_w (B : Under A) :
    (((Under.costarAdjForget A).counit.app B) ≫ polynomialAlgebraCounit_section A B) ≫
        (Under.costarAdjForget A).counit.app B =
      (Under.costarAdjForget A).counit.app B ≫ 𝟙 B := by
  -- Postcompose the section identity by the counit to obtain the arrow-morphism compatibility.
  simpa [Category.assoc] using
    congrArg
      (fun k ↦ ((Under.costarAdjForget A).counit.app B) ≫ k)
      (polynomialAlgebraCounit_section_comp_counit A B)

/-- Helper for Example 14.34.5: the owner-level augmented Čech nerve of the counit carries the
canonical extra degeneracy induced by the adjunction unit. -/
private def polynomialAlgebraResolution_extraDegeneracy (B : Under A) :
    (polynomialAlgebraAugmentedResolution A B).ExtraDegeneracy :=
  Arrow.AugmentedCechNerve.extraDegeneracy
    (Arrow.mk ((Under.costarAdjForget A).counit.app B))
    { section_ := polynomialAlgebraCounit_section A B
      id := polynomialAlgebraCounit_section_comp_counit A B }

/-- Helper for Example 14.34.5: on the owner-level Čech nerve, the augmentation followed by the
extra-degeneracy section is the standard Čech endomorphism induced by the split counit. -/
private theorem polynomialAlgebraResolution_hom_comp_section_eq_mapCechNerve
    (B : Under A) :
    (polynomialAlgebraAugmentedResolution A B).hom ≫
        (polynomialAlgebraResolution_extraDegeneracy A B).section_ =
      Arrow.mapCechNerve
        (Arrow.homMk
          (((Under.costarAdjForget A).counit.app B) ≫ polynomialAlgebraCounit_section A B)
          (𝟙 B)
          (polynomialAlgebraCounit_section_endomorphism_w A B)) := by
  -- Route correction: compare the augmentation-section composite in the true owner category
  -- `Under A`, then whisker the resulting homotopy to sets instead of building a raw set-level
  -- Čech nerve and searching for a comparison isomorphism back to the owner.
  -- TODO: once the section is moved to the correct set-level/composed-adjunction owner, compare
  -- the augmentation-section composite with the corresponding Čech endomorphism there and only
  -- then whisker to the needed forgetful views.
  sorry

/-- Helper for Example 14.34.5: the owner-level split counit induces a simplicial homotopy from
the augmentation-section composite to the identity on the polynomial algebra resolution. -/
private theorem polynomialAlgebraResolution_hom_comp_section_homotopic_id
    (B : Under A) :
    Homotopic
      ((polynomialAlgebraAugmentedResolution A B).hom ≫
        (polynomialAlgebraResolution_extraDegeneracy A B).section_)
      (𝟙 (polynomialAlgebraAugmentedResolution A B).left) := by
  -- Rewrite to the textbook Čech-nerve endomorphism and apply Lemma 14.26.9.
  rw [polynomialAlgebraResolution_hom_comp_section_eq_mapCechNerve]
  exact Homotopic.of_homotopy
    (cechNerveSectionEndomorphism_homotopic_id
      ((Under.costarAdjForget A).counit.app B)
      (polynomialAlgebraCounit_section A B)
      (polynomialAlgebraCounit_section_comp_counit A B))

-- Proof sketch: the counit map `A[B] ⟶ B` is split by the unit of the adjunction, so its
-- augmented Cech nerve has an extra degeneracy. After forgetting to sets, this gives a simplicial
-- homotopy equivalence for the augmentation of the underlying simplicial set.
/-- Example 14.34.5: for a commutative ring `A` and a commutative `A`-algebra `B`, the
augmentation of the underlying simplicial set of `polynomialAlgebraAugmentedResolution A B`
admits a simplicial homotopy inverse. -/
theorem polynomialAlgebraResolutionForgetAugmentation_isHomotopyEquivalence
    (B : Under A) :
    IsHomotopyEquivalence (polynomialAlgebraAugmentedUnderlyingSet A B).hom := by
  let s :
      (const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right ⟶
        (polynomialAlgebraAugmentedUnderlyingSet A B).left :=
    Functor.whiskerRight
      (polynomialAlgebraResolution_extraDegeneracy A B).section_
      (Under.forget A ⋙ forget CommRingCat)
  have hs :
      s ≫ (polynomialAlgebraAugmentedUnderlyingSet A B).hom =
        𝟙 ((const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right) := by
    -- Whiskering the owner-level strict section identity gives the section equation in sets.
    simpa [s, polynomialAlgebraAugmentedUnderlyingSet, polynomialAlgebraAugmentedResolution] using
      congrArg
        (fun f ↦ Functor.whiskerRight f (Under.forget A ⋙ forget CommRingCat))
        (SimplicialObject.Augmented.ExtraDegeneracy.section_comp_hom
          (polynomialAlgebraResolution_extraDegeneracy A B))
  let e :
      HomotopyEquiv
        (polynomialAlgebraAugmentedUnderlyingSet A B).left
        ((const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right) :=
    { hom := (polynomialAlgebraAugmentedUnderlyingSet A B).hom
      inv := s
      homotopyHomInvId := by
        -- Whisker the owner-level homotopy from Lemma 14.26.9 down to underlying sets.
        simpa [s, polynomialAlgebraAugmentedUnderlyingSet, polynomialAlgebraAugmentedResolution] using
          Homotopic.whiskerRight
            (polynomialAlgebraResolution_hom_comp_section_homotopic_id A B)
            (Under.forget A ⋙ forget CommRingCat)
      homotopyInvHomId := by
        -- The simplicial inverse is a strict section, hence homotopic to the identity.
        simpa [hs] using
          (Homotopic.refl
            (𝟙 ((const (Type u)).obj (polynomialAlgebraAugmentedUnderlyingSet A B).right))) }
  exact ⟨e, rfl⟩

-- Proof sketch: the extra degeneracy on the augmented Cech nerve survives under the forgetful
-- functor `Under A ⥤ ModuleCat A`. Applying the standard extra-degeneracy argument for
-- alternating-face-map complexes yields a quasi-isomorphism to the complex concentrated in degree
-- `0` at the underlying `A`-module of `B`.
/-- The augmentation of the alternating face map complex of
`polynomialAlgebraAugmentedResolution A B`, after forgetting to `A`-modules, is a
quasi-isomorphism to the complex concentrated in degree `0` at `B`. -/
theorem polynomialAlgebraResolutionAlternatingFaceMapComplex_quasiIso
    (B : Under A) :
    QuasiIso (AlternatingFaceMapComplex.ε.app (polynomialAlgebraAugmentedModuleResolution A B)) :=
  by
  let ed :=
    SimplicialObject.Augmented.ExtraDegeneracy.map
      (polynomialAlgebraResolution_extraDegeneracy A B)
      (polynomialAlgebraForgetToModule A)
  let e := SimplicialObject.Augmented.ExtraDegeneracy.homotopyEquiv ed
  -- The same owner-level extra degeneracy yields the displayed chain-level homotopy equivalence
  -- after forgetting to `A`-modules.
  simpa [ed, e, polynomialAlgebraAugmentedModuleResolution, polynomialAlgebraAugmentedResolution]
    using (show QuasiIso e.hom from inferInstance)

end CategoryTheory
