import Mathlib
import StacksProject_2024.Chap19.«19_2_6_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped DirectSum

universe u

/- Domain-style sampling for Lemma 19.2.7:
- primary domain: functoriality of pushouts and commutative squares in `ModuleCat R`;
- sampled owner API:
  `CategoryTheory.CommSq`,
  `pushout.map`,
  `baerModuleStep_square_commutes`,
  `𝐌(M)`,
  `𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R`;
- best owner abstraction: the natural transformation from the identity functor to the Baer
  one-step functor `M ↦ 𝐌(M)`, with source-facing square statements expressed as `CommSq`;
- primitive data: the Baer pushout span, its induced pushout maps, and the functorial
  `pushout.map`;
- derived API: the naturality squares and the resulting natural transformation.

Source/core/bridge triage:
- `source-facing`: the functoriality square for `M ⟶ \mathbf{M}(M)` and the extension square for
  ideal maps;
- `core/canonical`: `CommSq` for commuting squares and the natural transformation
  `𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R`;
- `bridge/view`: the explicit Baer pushout maps whose commutativity witnesses are packaged by
  those owner abstractions. -/

section

variable (R : Type u) [Ring R]

local notation "𝐌(" M ")" => baerModuleStep R M

/-- The map on Baer indices induced by an `R`-linear map of modules. -/
abbrev baerModuleIndexMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleIndex R M → baerModuleIndex R N :=
  fun j ↦ ⟨j.1, f.hom.comp j.2⟩

/-- The map on the direct sum of ideals induced by an `R`-linear map of modules. -/
noncomputable abbrev baerModuleIdealDirectSumMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleIdealDirectSum R M ⟶ baerModuleIdealDirectSum R N :=
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M)
      (⨁ j : baerModuleIndex R N, baerModuleIdealSummand R N j)
      (fun j ↦
        DirectSum.lof R (baerModuleIndex R N) (baerModuleIdealSummand R N)
          (baerModuleIndexMap R f j))

/-- The map on the direct sum of copies of `R` induced by an `R`-linear map of modules. -/
noncomputable abbrev baerModuleRingDirectSumMap {M N : ModuleCat R} (f : M ⟶ N) :
    baerModuleRingDirectSum R M ⟶ baerModuleRingDirectSum R N :=
  ModuleCat.ofHom <|
    DirectSum.toModule R (baerModuleIndex R M)
      (⨁ _j : baerModuleIndex R N, R)
      (fun j ↦
        DirectSum.lof R (baerModuleIndex R N) (fun _j ↦ R)
          (baerModuleIndexMap R f j))

/-- The left side of the Baer pushout square is natural in the module. -/
-- Proof sketch: both composites send the summand indexed by `(𝔞, φ)` to the copy of `R`
-- indexed by `(𝔞, f ∘ φ)` using the same inclusion `𝔞 ↪ R`, so they agree by extensionality of
-- maps out of a direct sum.
theorem baerModuleLeftVertical_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq (baerModuleLeftVertical R M) (baerModuleIdealDirectSumMap R f)
      (baerModuleRingDirectSumMap R f) (baerModuleLeftVertical R N) := sorry

/-- The top map in the Baer pushout square is natural in the module. -/
-- Proof sketch: on the summand indexed by `(𝔞, φ)`, the top map followed by `f` is exactly the
-- composite `f ∘ φ`, which is also the map defining the target summand indexed by `(𝔞, f ∘ φ)`.
theorem baerModuleTopMap_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq (baerModuleTopMap R M) (baerModuleIdealDirectSumMap R f) f
      (baerModuleTopMap R N) := sorry

/-- The map `\mathbf{M}(M) → \mathbf{M}(N)` induced by a morphism `M ⟶ N`. -/
noncomputable abbrev baerModuleStepMap {M N : ModuleCat R} (f : M ⟶ N) :
    𝐌(M) ⟶ 𝐌(N) :=
  pushout.map (baerModuleLeftVertical R M) (baerModuleTopMap R M)
    (baerModuleLeftVertical R N) (baerModuleTopMap R N)
    (baerModuleRingDirectSumMap R f) f (baerModuleIdealDirectSumMap R f)
    (baerModuleLeftVertical_natural R f).w (baerModuleTopMap_natural R f).w

/-- The canonical map on Baer pushouts acts as the identity on identity morphisms. -/
-- Proof sketch: this is the identity case of `pushout.map`, using the identity maps on all three
-- corners of the defining span.
theorem baerModuleStepMap_id (M : ModuleCat R) :
    baerModuleStepMap R (𝟙 M) = 𝟙 (𝐌(M)) := sorry

/-- The canonical map on Baer pushouts respects composition. -/
-- Proof sketch: functoriality of `pushout.map` gives the compatibility with composition once the
-- naturality relations for the two sides of the defining span are inserted.
theorem baerModuleStepMap_comp {M N P : ModuleCat R} (f : M ⟶ N) (g : N ⟶ P) :
    baerModuleStepMap R (f ≫ g) =
      baerModuleStepMap R f ≫ baerModuleStepMap R g := sorry

/-- The Baer construction `M ↦ \mathbf{M}(M)` as an endofunctor on `ModuleCat R`. -/
noncomputable def baerModuleStepFunctor : ModuleCat R ⥤ ModuleCat R where
  obj := baerModuleStep R
  map := baerModuleStepMap R
  map_id := baerModuleStepMap_id R
  map_comp := baerModuleStepMap_comp R

/-- The canonical extension map `R ⟶ \mathbf{M}(M)` attached to an ideal map `𝔞 → M`. -/
noncomputable abbrev baerModuleIdealLift (M : ModuleCat R) (I : Ideal R) (φ : I →ₗ[R] M) :
    ModuleCat.of R R ⟶ 𝐌(M) :=
  ModuleCat.ofHom
      (DirectSum.lof R (baerModuleIndex R M) (fun _j ↦ R) ⟨I, φ⟩) ≫
    baerModuleStepFromRingDirectSum R M

-- Proof sketch: the morphisms `baerModuleStepMap R f` assemble the one-step Baer construction
-- into an endofunctor, and the canonical inclusions from `M` into the pushouts commute with these
-- induced maps by the universal property of `pushout.map`.
/-- Lemma 19.2.7 (1): the canonical maps `M ⟶ \mathbf{M}(M)` are functorial in `M`. -/
theorem baerModuleStepInclusion_natural {M N : ModuleCat R} (f : M ⟶ N) :
    CommSq f (baerModuleStepInclusion R M) (baerModuleStepInclusion R N)
      ((baerModuleStepFunctor R).map f) := sorry

/-- The natural transformation from the identity functor on `R`-modules to the one-step Baer
functor. -/
noncomputable def baerModuleStepInclusionNatTrans :
    𝟭 (ModuleCat R) ⟶ baerModuleStepFunctor R where
  app M := baerModuleStepInclusion R M
  naturality := fun {_ _} f ↦ (baerModuleStepInclusion_natural R f).w

-- Proof sketch: in the Baer pushout construction one adjoins copies of `R` to force extensions of
-- maps from ideals into `M`, but no relation identifies two distinct elements already lying in
-- `M`; this yields injectivity of the canonical inclusion.
/-- Lemma 19.2.7 (2): the canonical map `M ⟶ \mathbf{M}(M)` is injective. -/
theorem baerModuleStepInclusion_injective (M : ModuleCat R) :
    Function.Injective (baerModuleStepInclusion R M).hom := sorry

-- Proof sketch: the pair `(I, φ)` indexing the chosen ideal map contributes a distinguished `R`
-- summand to the left side of the pushout, and composing its coprojection with the pushout map
-- produces the required extension square.
/-- Lemma 19.2.7 (3): every `R`-linear map from an ideal `I ⊆ R` to `M` extends to a map
`R ⟶ \mathbf{M}(M)` compatible with the canonical inclusion `M ⟶ \mathbf{M}(M)`. -/
theorem baerModuleIdealLift_comp_subtype (M : ModuleCat R) (I : Ideal R) (φ : I →ₗ[R] M) :
    CommSq (ModuleCat.ofHom I.subtype) (ModuleCat.ofHom φ)
      (baerModuleIdealLift R M I φ) (baerModuleStepInclusion R M) := sorry

end
