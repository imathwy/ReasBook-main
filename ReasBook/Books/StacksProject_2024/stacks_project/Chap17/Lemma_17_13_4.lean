import Mathlib
import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_13_1

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

/-
Domain-style sampling for Lemma 17.13.4:
- primary domain: pushforward and pullback of sheaves of modules along a morphism of ringed
  spaces, together with the adjunction and essential-image package for a fully faithful right
  adjoint;
- inspected owner declarations:
  `RingedSpace.IsClosedImmersion`,
  `Topology.IsClosedEmbedding`,
  `Sheaf.IsLocallySurjective`,
  `RingedSpace.Hom.pushforward`,
  `SheafOfModules.pullbackPushforwardAdjunction`;
- best owner abstraction: the source-facing closed-immersion owner `RingedSpace.IsClosedImmersion
  i`, whose module-theoretic consequences are expressed on the canonical pushforward owner `i _*`;
- primitive data: a morphism `i : Z ⟶ X`, the closed-embedding condition on `i.hom.base`, and the
  local surjectivity of `𝒪_X ⟶ i_* 𝒪_Z`;
- derived API: exactness, the canonical `FullyFaithful` structure on `i _*`, the source-facing
  ideal-sheaf annihilation criterion, and its adjunction-theoretic unit-isomorphism
  reformulation.

Source/core/bridge triage:
- `source-facing`: the Stacks Project assertions about pushforward of module sheaves along a
  closed immersion of ringed spaces;
- `core/canonical`: `Topology.IsClosedEmbedding i.hom.base`,
  `Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)`,
  `SheafOfModules.pushforward (RingedSpace.Hom.toRingCatSheafHom i)`, and
  `SheafOfModules.pullbackPushforwardAdjunction (RingedSpace.Hom.toRingCatSheafHom i)`;
- `bridge/view`: `RingedSpace.IsClosedImmersion i`, which packages the two hypotheses above with
  extra local-generators data not used in this lemma. -/

namespace AlgebraicGeometry

section

variable {X Z : RingedSpace.{u}} (i : Z ⟶ X)

local notation "φi" => RingedSpace.Hom.toRingCatSheafHom i

-- Proof sketch: combine the exactness of pushforward on underlying abelian sheaves for a closed
-- subset inclusion with the exactness of restriction of scalars on sections defining module
-- pushforward.
/-- Lemma 17.13.4 (1): if `i : (Z, \mathcal O_Z) \to (X, \mathcal O_X)` has underlying map a
closed embedding, then the pushforward functor on module sheaves is exact. -/
theorem ringedSpaceModulePushforward_exact_of_isClosedEmbedding
    (hi : Topology.IsClosedEmbedding i.hom.base) :
    exactFunctor Z.Modules X.Modules (i _*) := sorry

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the canonical exactness statement for pushforward of module sheaves. -/
theorem ringedSpaceModulePushforward_exact_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i] :
    exactFunctor Z.Modules X.Modules (i _*) := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact ringedSpaceModulePushforward_exact_of_isClosedEmbedding i hi.isClosedEmbedding

-- Proof sketch: prove that the counit `i^* i_* ℱ ⟶ ℱ` is an isomorphism on stalks using the
-- closed-embedding hypothesis and the quotient description of local rings; then apply the standard
-- criterion that a right adjoint with isomorphic counit is fully faithful.
/-- Lemma 17.13.4 (2): under the same hypotheses, the pushforward functor on module sheaves is
fully faithful. -/
noncomputable instance
    ringedSpaceModulePushforward_fullyFaithful_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)] :
    (i _*).FullyFaithful := sorry

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the canonical fully faithful structure on pushforward of module sheaves. -/
noncomputable instance ringedSpaceModulePushforward_fullyFaithful_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i] : (i _*).FullyFaithful :=
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  ringedSpaceModulePushforward_fullyFaithful_of_isClosedEmbedding_of_isLocallySurjective i
    hi.isClosedEmbedding

-- Proof sketch: if `𝒢 ≅ i_* ℱ`, then every local section of the kernel ideal sheaf maps to zero
-- in `i_* \mathcal O_Z`, hence acts trivially on local sections of `𝒢`. Conversely, triviality of
-- that ideal action is the source-facing condition allowing the module structure on `𝒢` to
-- descend from `X` to the closed subspace `Z`.
/-- Lemma 17.13.4 (3): under the same hypotheses, an `\mathcal O_X`-module sheaf lies in the
essential image of `i_*` exactly when the ideal sheaf of the closed embedding acts trivially on
it, i.e. every local section of `\mathcal I` acts by zero on local sections of `\mathcal G`. -/
theorem
    ringedSpaceModulePushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      ∀ U : Opens X,
        ∀ s : (RingedSpace.closedImmersionIdealSheaf i).val.obj (op U),
          ∀ m : 𝒢.val.obj (op U),
            ((kernel.ι
                (SheafOfModules.unitToPushforwardObjUnit φi)).val.app (op U) s) • m = 0 := sorry

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` supplies
the essential-image criterion for module pushforward in terms of annihilation by the ideal sheaf
of the closed immersion. -/
theorem
    ringedSpaceModulePushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      ∀ U : Opens X,
        ∀ s : (RingedSpace.closedImmersionIdealSheaf i).val.obj (op U),
          ∀ m : 𝒢.val.obj (op U),
            ((kernel.ι
                (SheafOfModules.unitToPushforwardObjUnit φi)).val.app (op U) s) • m = 0 := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact
    ringedSpaceModulePushforward_essImage_iff_closedImmersionIdealSheaf_smul_eq_zero_of_isClosedEmbedding_of_isLocallySurjective
      i hi.isClosedEmbedding 𝒢

-- Proof sketch: for a fully faithful right adjoint, an object lies in the essential image exactly
-- when the adjunction unit is an isomorphism. The previous theorem is the source-facing
-- closed-immersion translation of that generic adjunction criterion.
/-- Companion reformulation: under the same hypotheses, the essential-image criterion can
equivalently be phrased by asking that the adjunction unit
`\mathcal G \to i_* i^* \mathcal G` be an isomorphism. -/
theorem ringedSpaceModulePushforward_essImage_iff_unit_isIso_of_isClosedEmbedding_of_isLocallySurjective
    (hi : Topology.IsClosedEmbedding i.hom.base)
    [Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i)]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) := by
  let _ : Sheaf.IsLocallySurjective (RingedSpace.Hom.commRingSheafPushforwardMap i) :=
    inferInstance
  let hFF : (SheafOfModules.pushforward φi).FullyFaithful := by
    change (i _*).FullyFaithful
    exact
      ringedSpaceModulePushforward_fullyFaithful_of_isClosedEmbedding_of_isLocallySurjective i hi
  letI : (SheafOfModules.pushforward φi).Full := hFF.full
  letI : (SheafOfModules.pushforward φi).Faithful := hFF.faithful
  simpa using
    (((SheafOfModules.pullbackPushforwardAdjunction φi).isIso_unit_app_iff_mem_essImage :
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) ↔
        (SheafOfModules.pushforward φi).essImage 𝒢)).symm

/-- Closed-immersion bridge: the source-facing owner `RingedSpace.IsClosedImmersion i` also
supplies the canonical adjunction-unit reformulation of the essential-image criterion. -/
theorem ringedSpaceModulePushforward_essImage_iff_unit_isIso_of_isClosedImmersion
    [RingedSpace.IsClosedImmersion i]
    (𝒢 : X.Modules) :
    (i _*).essImage 𝒢 ↔
      IsIso ((SheafOfModules.pullbackPushforwardAdjunction φi).unit.app 𝒢) := by
  let hi : RingedSpace.IsClosedImmersion i := inferInstance
  exact
    ringedSpaceModulePushforward_essImage_iff_unit_isIso_of_isClosedEmbedding_of_isLocallySurjective
      i hi.isClosedEmbedding 𝒢

end

end AlgebraicGeometry
