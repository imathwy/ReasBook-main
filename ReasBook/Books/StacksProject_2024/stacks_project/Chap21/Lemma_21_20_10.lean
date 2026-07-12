import StacksProject_2024.Chap13.Lemma_13_31_9
import StacksProject_2024.Chap18.Definition_18_31_1
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open scoped RingedSite.Hom

noncomputable section

universe u v

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.20.10:
- primary domain: K-injective cochain complexes of module sheaves under flat direct image on
  ringed sites;
- sampled owner declarations:
  `RingedSite.Hom.IsFlat`,
  `RingedSite.Hom.modulePushforward`,
  `RingedSite.Hom.(^*)`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction: the source-facing ringed-site direct image `f.modulePushforward` for a
  flat morphism `f : X ⟶ Y`.

Source/core/bridge triage:
- `source-facing`: a flat morphism of ringed sites sends K-injective complexes of `𝒪_X`-modules
  to K-injective complexes of `𝒪_Y`-modules under direct image;
- `core/canonical`: the Chapter 13 theorem
  `right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: the pullback-pushforward adjunction `f^* ⊣ f.modulePushforward` together with
  exactness of `f^*` supplied by `IsFlat.pullback_exact`.

The public API should therefore live on the ringed-site direct-image owner `f.modulePushforward`,
not on a second abstract wrapper around the Chapter 13 theorem.
-/

section

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{max u v}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]

local notation "ModX" => SheafOfModules X.structureSheaf
local notation "ModY" => SheafOfModules Y.structureSheaf

/-- Helper for Lemma 21.20.10: the source-facing direct-image functor `f _*` preserves
K-injective cochain complexes when `f` is flat. -/
private theorem modulePushforwardComplexIsKInjective
    [Fact (IsFlat f)] (I : CochainComplex ModX ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((f _*).mapHomologicalComplex (up ℤ)).obj I) := by
  -- Proof comment: apply the Chapter 13 right-adjoint criterion directly to the canonical
  -- pullback-pushforward adjunction for `f`.
  exact right_adjoint_preserves_isKInjective_of_exact_left_adjoint
    (f _*)
    (f^*)
    (SheafOfModules.pullbackPushforwardAdjunction f.structureSheafMap)
    (IsFlat.pullback_exact f Fact.out)
    I

/-- Lemma 21.20.10: for a flat morphism of ringed sites `f : X ⟶ Y`, the direct image of a
K-injective cochain complex of `𝒪_X`-modules is K-injective as a cochain complex of
`𝒪_Y`-modules. -/
@[stacks 093Y]
theorem modulePushforwardComplex_isKInjective_of_isFlat
    (hf : IsFlat f) (I : CochainComplex ModX ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((f _*).mapHomologicalComplex (up ℤ)).obj I) := by
  -- Proof comment: package the explicit flatness hypothesis as the typeclass input expected by
  -- the helper theorem.
  let _ : Fact (IsFlat f) := ⟨hf⟩
  -- Proof comment: the helper already targets the source-facing direct-image owner.
  exact modulePushforwardComplexIsKInjective (f := f) I

end

end RingedSite.Hom
