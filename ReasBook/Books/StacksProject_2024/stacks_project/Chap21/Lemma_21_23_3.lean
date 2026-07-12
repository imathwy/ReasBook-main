import StacksProject_2024.Chap19.Lemma_19_13_6
import StacksProject_2024.Chap21.Lemma_21_19_1_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped RingedSiteDerived

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite.Hom

/- Domain-style sampling for Lemma 21.23.3:
- primary domain: preservation of sequential derived limits by the derived direct-image functor on
  module sheaves over a ringed site;
- sampled owner declarations:
  `CategoryTheory.IsDerivedLimit`,
  `CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit`,
  `RingedSite.Hom.pushforward`,
  `R(f)_*`,
  `RingedSite.Hom.modulePushforwardDerived`;
- best owner abstraction:
  `source-facing`: the ringed-site specialization saying the chosen total right derived direct
    image `R(f)_*` commutes with derived limits;
  `core/canonical`: the Chapter 19 owner
    `CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit`, specialized to the
    underived module pushforward `f.pushforward` whose total right derived functor is the
    Chapter 21 owner `R(f)_*`;
  `bridge/view`: this theorem, which records the ringed-site specialization directly on the
    source-facing derived-pushforward notation rather than a parallel local total-right-derived
    wrapper.
- primitive data: the morphism `f`, the inverse system `Ksys`, and the chosen derived-limit
  witness `hK`;
- derived API: the stagewise image tower under `R(f)_*` and the resulting
  derived-limit witness. -/

section

variable {X Y : RingedSite.{u, v}} (f : RingedSite.Hom X Y)

local notation "ModX" => ModuleCat X
local notation "ModY" => ModuleCat Y
local notation "DModX" => ModuleDerived X

-- Proof sketch: represent the inverse system by an object of the derived category of sequential
-- inverse systems, apply the site-theoretic description of `R lim` from Lemma `21.23.1`, and use
-- the commutative square relating `f_*` and the projection from `X × ℕ` to `X`. Equivalently, one
-- can apply `Rf_*` to the Milnor distinguished triangle defining the derived limit and use that
-- `Rf_*` is a right adjoint, hence preserves products.
/-- Lemma 21.23.3: for a morphism of ringed topoi, formalized here by a morphism of ringed sites
`f : X ⟶ Y`, the derived direct image functor `R(f)_*` commutes with derived limits of sequential
inverse systems. Concretely, if `K` is a derived limit of a tower `(K_n)` in `D(𝒪_X)`, then
`R(f)_* K` is a derived limit of the pushed-forward tower `(R(f)_* K_n)` in `D(𝒪_Y)`. -/
@[stacks 0A07]
theorem modulePushforwardDerived_preservesDerivedLimit
    [f.pushforward.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) f.pushforward]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
    [IsGrothendieckAbelian.{max u v} ModX]
    [HasCountableProducts ModY]
    [CountableAB4Star ModY]
    {Ksys : SequentialInverseSystem DModX} {K : DModX}
    (hK : IsDerivedLimit Ksys K) :
    IsDerivedLimit
      (Ksys ⋙ R(f)_*)
      ((R(f)_*).obj K) := by
  simpa
      [CategoryTheory.additiveFunctorTotalRightDerived, RingedSite.Hom.pushforward,
        RingedSite.Hom.modulePushforwardToDerived, RingedSite.Hom.modulePushforwardDerived] using
    (CategoryTheory.additiveFunctor_totalRightDerived_preservesDerivedLimit
      f.pushforward hK)

end

end RingedSite.Hom
