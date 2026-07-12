import StacksProject_2024.Chap13.Definition_13_34_1
import StacksProject_2024.Chap20.Lemma_20_32_3
import StacksProject_2024.Chap20.Lemma_20_32_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry.RingedSpaceCohomology
open scoped RingedSpaceDerivedSectionsAtOpenToAb

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})

local instance : IsGrothendieckAbelian.{u} (RingedSpace.Modules X) :=
  sheafModules_isGrothendieckAbelian X

local notation "DModX" => DerivedCategory X.Modules
local notation "HMod" p:max => DerivedCategory.homologyFunctor X.Modules p
local notation "H" p:max => DerivedCategory.homologyFunctor AddCommGrpCat p

/- Domain-style sampling for Lemma 20.37.5:
- primary domain: stalkwise injectivity criteria coming from Milnor short exact sequences for
  derived sections over shrinking open neighborhoods;
- sampled owner declarations:
  `RingedSpace.cohomologySheaf`,
  `𝓗[m](X, K)`,
  `moduleUnderlyingSheaf`,
  `moduleSectionsAsAbelianFunctor`,
  `moduleDerivedSectionsAtOpenToAb`,
  `SequentialInverseSystem.firstDerivedLimit`,
  `HasMilnorTriangle.WithMap`,
  `DerivedCategory.homologyFunctor`,
  `TopCat.Presheaf.stalkFunctor`;
- best owner abstraction in the minimal compilable Chapter 20 closure:
  the Chapter 20 cohomology-sheaf owner `𝓗[m](X, -)` together with
  `moduleDerivedSectionsAtOpenToAb X U`, the Chapter 13 Milnor-triangle owner
  `HasMilnorTriangle.WithMap`, and the canonical stalk functor on additive sheaves;
- primitive data: the inverse system `Ksys`, the chosen Milnor comparison map `ι` into the
  product, the point `x`, the stage `n(x)`, and the neighborhood-shrinking local hypotheses;
- derived API:
  `SequentialInverseSystem.firstDerivedLimit
    ((Ksys ⋙ moduleDerivedSectionsAtOpenToAb X U) ⋙ H^m)`, the canonical cohomology-sheaf map
  `((moduleUnderlyingSheaf X).map ((HMod m).map (ι ≫ Pi.π ... n(x))))`, and its stalk map via
  `TopCat.Presheaf.stalkFunctor`.

Source/core/bridge triage:
- `source-facing`: the stalkwise injectivity criterion itself, with its explicit Milnor
  comparison data and shrinking-neighborhood hypotheses;
- `core/canonical`: `𝓗[m](X, -)`, `moduleDerivedSectionsAtOpenToAb`,
  `SequentialInverseSystem.firstDerivedLimit`, `HasMilnorTriangle.WithMap`,
  `DerivedCategory.homologyFunctor`, and `TopCat.Presheaf.stalkFunctor`;
- `bridge/view`: the direct stalk map obtained by applying `TopCat.Presheaf.stalkFunctor` to the
  canonical cohomology-sheaf morphism; no additional owner is introduced here.
-/

/-- The canonical degree-`m` cohomology-sheaf map from the Milnor comparison object `K` to the
stage `K_{nx}`. -/
def cohomologySheafStageMap
    (Ksys : SequentialInverseSystem DModX)
    (K : DModX) (m : ℤ) (nx : ℕ)
    [HasProduct (inverseSystemFamily Ksys)]
    (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys) :
    𝓗[m](X, K) ⟶ 𝓗[m](X, Ksys.obj (op nx)) :=
  (moduleUnderlyingSheaf X).map ((HMod m).map (ι ≫ Pi.π (inverseSystemFamily Ksys) nx))

-- Proof sketch: represent a germ in the stalk of `H^m(K)` by a section over an open neighborhood
-- coming from the cofinal neighborhood system in the hypotheses. Using the sheafification
-- description of cohomology sheaves from Lemma `20.32.3`, shrink so that its image in the stage
-- `n(x)` stalk is already zero on that neighborhood. Then apply the Milnor short exact sequence
-- from `20.37.3.1`: the local `R^1 lim` term vanishes, and the local transition maps into stage
-- `n(x)` are injective, forcing the representing section itself to vanish.
/-- Lemma 20.37.5, categorical stalk form: under the local Milnor vanishing and eventual
injectivity hypotheses, the stalk map of the canonical cohomology-sheaf stage morphism is a
monomorphism. -/
@[stacks 0D61]
theorem cohomologyStalkMap_mono_to_eventual_stage_of_local_milnor_conditions
    (Ksys : SequentialInverseSystem DModX)
    (K : DModX)
    (x : X) (m : ℤ) (nx : ℕ)
    [HasProduct (inverseSystemFamily Ksys)]
    (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (hlocal :
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧
            U ≤ W ∧
            IsZero (SequentialInverseSystem.firstDerivedLimit ((Ksys ⋙ RΓ[U]) ⋙ H (m - 1))) ∧
            ∀ n : ℕ, ∀ hn : nx ≤ n,
              Mono (SequentialInverseSystem.transitionMap (((Ksys ⋙ RΓ[U]) ⋙ H m)) hn)) :
    Mono
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (cohomologySheafStageMap X Ksys K m nx ι).hom) := by
  let _ := hι
  let _ := hlocal
  sorry

/-- Lemma 20.37.5: let `(X, 𝒪_X)` be a ringed space, let `(K_n)` be a sequential inverse system
in `D(𝒪_X)`, let `x ∈ X`, and let `m ∈ ℤ`. Assume there is an index `n(x)` such that every open
neighborhood of `x` contains a smaller open neighborhood `U` with
`R¹ limₙ H^(m - 1)(U, K_n) = 0` and such that the transition maps
`H^m(U, K_n) ⟶ H^m(U, K_{n(x)})` are injective for all `n ≥ n(x)`. Then the induced map on
stalks `H^m(R limₙ K_n)_x ⟶ H^m(K_{n(x)})_x`, formalized by the canonical stage map
`ι ≫ Pi.π (inverseSystemFamily Ksys) nx`, is injective. -/
@[stacks 0D61]
theorem cohomologyStalkMap_injective_to_eventual_stage_of_local_milnor_conditions
    (Ksys : SequentialInverseSystem DModX)
    (K : DModX)
    (x : X) (m : ℤ) (nx : ℕ)
    [HasProduct (inverseSystemFamily Ksys)]
    (ι : K ⟶ ∏ᶜ inverseSystemFamily Ksys)
    (hι : HasMilnorTriangle.WithMap Ksys ι)
    (hlocal :
      ∀ W : Opens X.carrier, x ∈ W →
        ∃ U : Opens X.carrier,
          x ∈ U ∧
            U ≤ W ∧
            IsZero (SequentialInverseSystem.firstDerivedLimit ((Ksys ⋙ RΓ[U]) ⋙ H (m - 1))) ∧
            ∀ n : ℕ, ∀ hn : nx ≤ n,
              Mono (SequentialInverseSystem.transitionMap (((Ksys ⋙ RΓ[U]) ⋙ H m)) hn)) :
    Function.Injective
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        (cohomologySheafStageMap X Ksys K m nx ι).hom) := by
  exact
    (AddCommGrpCat.mono_iff_injective _).1
      (cohomologyStalkMap_mono_to_eventual_stage_of_local_milnor_conditions
        X Ksys K x m nx ι hι hlocal)

end

end AlgebraicGeometry.RingedSpace
