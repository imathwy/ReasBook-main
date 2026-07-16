import StacksProject_2024.stacks_project.Chap21.Lemma_21_19_1_core
import StacksProject_2024.stacks_project.Chap21.Definition_21_47_1

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open scoped RingedSite.Hom RingedSiteDerived

noncomputable section

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

universe u v

namespace RingedSite.Hom

section

/- Domain-style sampling for Lemma 21.47.5:
- primary domain: perfect objects in derived categories of module sheaves on ringed sites and
  their stability under derived pullback;
- sampled owner declarations:
  `modulePullbackDerived`,
  `RingedSite.Hom.ModuleDerived.IsPerfect`,
  `RingedSite.CochainComplex.IsPerfect`,
  `SheafOfModules.RingedSite.CochainComplex.isStrictlyPerfect_pullback`,
  `SheafOfModules.RingedSite.cochainComplex_isPerfect_of_represents_isPerfect`;
- best owner abstraction:
  `source-facing`: the bundled pullback theorem for a morphism `f : X ⟶ Y`;
  `core/canonical`: `modulePullbackDerived f` and `RingedSite.Hom.ModuleDerived.IsPerfect`;
  `bridge/view`: local strictly perfect representatives of perfect complexes, together with the
    comparison from a representing complex to the canonical derived object.
- primitive data: the ringed-site morphism `f`, the derived object `E`, and the perfectness
  witness on `E`;
- derived API: preservation of perfectness under `L(f)^*`. -/

variable {X Y : RingedSite.{u, v}} (f : X ⟶ Y)

variable [HasBinaryProducts X.carrier] [HasBinaryProducts Y.carrier]
variable [(PresheafOfModules.pushforward.{max u v} f.structureSheafMap.hom).IsRightAdjoint]
variable [(f^*).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]

-- Proof sketch: choose a perfect representative complex for `E` from Definition `21.47.1`. Its
-- local strictly perfect models remain strictly perfect after underived pullback by
-- Lemma `21.44.4`. Using the comparison between a perfect derived object and any representing
-- complex from Lemma `21.47.2`, these pulled-back local models witness perfectness of `L(f)^*E`.
/-- Lemma 21.47.5: for a morphism `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` of ringed sites, if `E` is a perfect
object of `D(𝒪_Y)`, then its derived pullback `L(f)^*E` is perfect in `D(𝒪_X)`. -/
@[stacks 08H6]
theorem modulePullbackDerived_isPerfect
    (E : ModuleDerived Y) (hE : E.IsPerfect) :
    ((L(f)^*).obj E).IsPerfect := by
  sorry

end

end RingedSite.Hom
