import StacksProject_2024.stacks_project.Chap19.Lemma_19_13_6
import StacksProject_2024.stacks_project.Chap20.«20_14_1_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry
open scoped RingedSpace.Hom RingedSpaceDerivedPushforward

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [(f _*).Additive]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Domain-style sampling for Lemma 20.37.2:
- primary domain: sequential derived inverse limits in derived categories of module sheaves on
  ringed spaces, and their behavior under derived pushforward;
- sampled owner declarations:
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit`,
  `R(f)_*`;
- best owner abstraction:
  `source-facing`: the specialization of derived-limit preservation to the ringed-space derived
    pushforward `R(f)_*`, surfaced in Lean by the canonical owner `R(f)_*`;
  `core/canonical`: the Chapter 13 tower owner `SequentialInverseSystem` together with
    `IsDerivedLimit`, and the Chapter 19 preservation theorem for additive total right derived
    functors;
  `bridge/view`: the ringed-space pushforward owner `f _*` on module sheaves and its total right
    derived functor `R(f)_*`.

Primitive data are only the morphism `f : X ⟶ Y`, the sequential inverse system `Ksys`, and the
chosen derived-limit witness for `K`. The Milnor product family, difference map, and the derived
pushforward functor already exist upstream as owner API, so this file should reuse those owners
directly rather than duplicating them locally. The Grothendieck-abelian structure on `X.Modules`,
the countable-product exactness on `Y.Modules`, and the limit preservation of `f_*` are canonical
proof support supplied by instance search, not source-facing theorem inputs. -/

-- Proof sketch: specialize the Chapter 19 preservation theorem for additive total right derived
-- functors to the underived module pushforward `f _*`, then rewrite the resulting owner
-- `additiveFunctorTotalRightDerived (f _*)` as the source-facing notation `R(f)_*`.
/-- Lemma 20.37.2: if `K` is a derived limit of an inverse system `Ksys` in `D(𝒪_X)`,
then `R(f)_* K` is a derived limit of the termwise direct-image system. Equivalently, the derived
pushforward functor `R(f)_*` commutes with derived limits. -/
@[stacks 0BKP]
theorem moduleDerivedPushforward_preservesDerivedLimits
    {Ksys : SequentialInverseSystem DModX} {K : DModX}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ R(f)_*)
      ((R(f)_*).obj K) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
