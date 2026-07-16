import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1
import StacksProject_2024.stacks_project.Chap20.Lemma_20_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.49.6:
- primary domain: perfect objects in derived categories of module sheaves on ringed spaces and
  their stability under derived pullback;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.DerivedCategory.IsPerfect`,
  `AlgebraicGeometry.RingedSpace.modulePullbackDerived`,
  `AlgebraicGeometry.RingedSpace.DerivedCategory.isPerfect_iff_exists_openCover`,
  `RingedSite.Hom.modulePullbackDerived_isPerfect`;
- best owner abstraction:
  `source-facing`: the ringed-space pullback statement for `L(f)^*`;
  `core/canonical`: the ringed-site owner theorem
    `RingedSite.Hom.modulePullbackDerived_isPerfect`;
  `bridge/view`: the opens ringed site of a ringed space together with the identification of the
    ringed-space perfectness predicate and derived pullback with the corresponding ringed-site
    owners.
- primitive vs. derived:
  primitive data are the morphism `f`, the derived object `E`, and the perfectness witness on `E`;
  the preservation statement is derived API over the Chapter 20 owners
  `modulePullbackDerived` and `DerivedCategory.IsPerfect`; the local-cover criterion from
  Definition `20.49.1` and the ringed-site owner theorem remain proof-side bridge
  infrastructure rather than this file's public API. -/

/-- Lemma 20.49.6: let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `E` be
an object of `D(𝒪_Y)`. If `E` is perfect in `D(𝒪_Y)`, then the derived pullback `L(f)^*E` is
perfect in `D(𝒪_X)`. -/
@[stacks 09UA]
theorem modulePullbackDerived_isPerfect
    [CategoryWithHomology (Modules X)] [CategoryWithHomology (Modules Y)]
    (f : X ⟶ Y) [(f^*).Additive]
    (E : DerivedCategory (Modules Y)) (hE : DerivedCategory.IsPerfect E) :
    DerivedCategory.IsPerfect ((L(f)^*).obj E) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
