import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap13.Definition_13_34_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_34_3
import StacksProject_2024.stacks_project.Chap20.Sections_on_open
import StacksProject_2024.stacks_project.Chap20.Lemma_20_37_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.SequentialInverseSystem
open Opposite
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpaceDerivedSectionsAtOpenToAb

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

/-
Domain-style sampling for Lemma 20.37.4:
- primary domain: derived inverse limits of towers of `𝒪_X`-modules and their openwise
  hypercohomology on basis opens;
- sampled owner declarations:
  `Opens.IsBasis`,
  `moduleSectionsAsAbelianFunctor`,
  `moduleDerivedSectionsAtOpenToAb`,
  `derivedSectionsAtOpenCohomology`,
  `CategoryTheory.IsDerivedLimit`,
  `SequentialInverseSystem.firstDerivedLimit`;
- best owner abstraction: the chapter owners `moduleSectionsAsAbelianFunctor X U` for sections on
  a fixed open subset and `moduleDerivedSectionsAtOpen X U` for open derived sections, viewed in
  `D(Ab)` through `moduleDerivedSectionsAtOpenToAb X U`; the later shorthand
  `derivedSectionsAtOpenCohomology X U` is built from the same owner, while the topological owner
  for a basis of opens is the canonical predicate `Opens.IsBasis`. The canonical Milnor term is
  `(ℱ ⋙ moduleSectionsAsAbelianFunctor X U).firstDerivedLimit`;
- primitive data: the tower `ℱ : ℕᵒᵖ ⥤ X.Modules`, the basis `ℬ` with basis hypothesis
  `Opens.IsBasis ℬ`, and the basiswise acyclicity / first-derived-inverse-limit hypotheses;
- derived API: openwise hypercohomology of the degree-zero derived objects and the derived-limit
  comparison theorem.

Source/core/bridge triage:
- `source-facing`: the two basiswise acyclicity statements of Lemma `20.37.4`;
- `core/canonical`: `Opens.IsBasis`, `moduleSectionsAsAbelianFunctor`,
  `moduleDerivedSectionsAtOpenToAb`, `IsDerivedLimit`, and
  `SequentialInverseSystem.firstDerivedLimit`;
- `bridge/view`: `derivedSectionsAtOpenCohomology`, which is a later chapter shorthand for the
  same open derived-sections owner. The source-facing theorems below use the owner directly rather
  than reintroducing a parallel local cohomology wrapper.
-/

-- The ambient category is `Mod(𝒪_X)` for the fixed ringed space `X`.
variable [IsGrothendieckAbelian.{u} X.Modules]
variable [CategoryWithHomology X.Modules]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor (DerivedCategory X.Modules) n)]

variable (ℱ : ℕᵒᵖ ⥤ X.Modules) (ℬ : Set (Opens X.carrier))

local notation "DModX" => DerivedCategory X.Modules
local notation "H" p:max => DerivedCategory.homologyFunctor AddCommGrpCat p
local notation "single₀" => DerivedCategory.singleFunctor X.Modules (0 : ℤ)

variable
  (hℬ : Opens.IsBasis ℬ)
  (hacyclic :
    ∀ (U : Opens X.carrier), U ∈ ℬ →
      ∀ (n p : ℕ), 0 < p →
        IsZero
          ((H(p : ℤ)).obj
            ((RΓ[U]).obj
              ((single₀).obj (ℱ.obj (op n))))))
  (hR1 :
    ∀ (U : Opens X.carrier), U ∈ ℬ →
      IsZero
        (SequentialInverseSystem.firstDerivedLimit
          (ℱ ⋙ moduleSectionsAsAbelianFunctor X U)))

-- Proof sketch: apply the openwise Milnor short exact sequence from `20.37.3.1` to the tower
-- `ℱₙ[0]`. On each `U ∈ ℬ`, positive stagewise cohomology vanishes by `hacyclic`, while
-- the first derived inverse-limit term for sections vanishes by `hR1`, so the objectwise
-- cohomology of the
-- derived limit is concentrated in degree `0` with degree-zero part equal to the ordinary inverse
-- limit presheaf. Since `ℬ` is a basis of opens, the needed coverings by members of `ℬ` are
-- available internally, and sheafification gives the same
-- statement for cohomology sheaves, hence the derived limit is represented by `limit ℱ` in degree
-- zero.
include hℬ hacyclic hR1 in
/-- Lemma 20.37.4 (1): if `ℬ` is a basis of opens of `X`, if `H^p(U, ℱₙ) = 0` for every
`U ∈ ℬ`, every `n`, and every `p > 0`, and if the inverse system of sections `ℱₙ(U)`
has vanishing first derived inverse limit for every `U ∈ ℬ`, then
the ordinary inverse limit sheaf `limit ℱ` computes the derived inverse limit
of the tower `(ℱₙ)`. -/
@[stacks 0BKS]
theorem single_limit_isDerivedLimit_of_basis_acyclicity :
    IsDerivedLimit
      (ℱ ⋙ single₀)
      ((single₀).obj (limit ℱ)) := by
  sorry

-- Proof sketch: apply the Milnor short exact sequence from `20.37.3.1` to the degree-zero tower
-- `ℱₙ[0]` and to the derived limit identified in part `(1)` with `(limit ℱ)[0]`. For `U ∈ ℬ` and
-- `p > 0`, the right term `lim H^p(U, ℱₙ)` vanishes by `hacyclic`, and the left first derived
-- inverse-limit term vanishes by `hR1` when `p = 1` and by the stagewise vanishing in degree
-- `p - 1` when `p > 1`. Hence `H^p(U, limit ℱ) = 0`.
include hℬ hacyclic hR1 in
/-- Lemma 20.37.4 (2): under the same hypotheses, the inverse limit sheaf
`limit ℱ` has vanishing higher cohomology on every open set `U ∈ ℬ`; that is,
`H^p(U, limit ℱ) = 0` for all `p > 0`. -/
@[stacks 0BKS]
theorem higherCohomologyAtBasisOpen_isZero_of_basis_acyclicity
    (U : Opens X.carrier) (hU : U ∈ ℬ) (p : ℕ) (hp : 0 < p) :
    IsZero ((H(p : ℤ)).obj ((RΓ[U]).obj ((single₀).obj (limit ℱ)))) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
