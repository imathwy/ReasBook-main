import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_82_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace LinearMap

noncomputable section

open IsLocalization

/-
Domain-style sampling:
- primary domain: universal injectivity of linear maps under restriction of scalars and
  localization of modules;
- sampled owner declarations:
  `LinearMap.UniversallyInjective`,
  `LinearMap.restrictScalars`,
  `Module.restrictScalars`,
  `IsScalarTower.restrictScalars`,
  `LocalizedModule.map`;
- best owner abstraction: the core owner is `LinearMap.UniversallyInjective`, with localization
  and scalar restriction handled by the canonical bridge APIs above rather than theorem-local
  wrapper maps;
- primitive data: a linear map together with the ambient scalar towers and localization map;
- derived API: the universally injective restricted-scalar views of localized maps and of
  `Localization S'`-linear maps.

Source/core/bridge triage:
- `source-facing`: Lemma `10.82.12`, comparing universal injectivity before and after localizing;
- `core/canonical`: `LinearMap.UniversallyInjective`;
- `bridge/view`: `LinearMap.restrictScalars`, `Module.restrictScalars`,
  `IsScalarTower.restrictScalars`, and `LocalizedModule.map`.
-/

section

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [Algebra A B]
variable {S : Submonoid A} {S' : Submonoid B}

variable {M : Type w} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
variable {M' : Type x} [AddCommGroup M'] [Module A M'] [Module B M'] [IsScalarTower A B M']

/-- Lemma 10.82.12 (1): if a `B`-linear map is universally injective as a map of `A`-modules,
then its localization at `S'` is universally injective as a map of `A`-modules. -/
-- Proof sketch: tensor the localized map with an arbitrary `A`-module, identify the result
-- with the localization of the tensor map over `A`, and use exactness of localization to
-- preserve injectivity.
theorem universallyInjective_localizedModule_restrictScalars
    (f : M →ₗ[B] M') (hf : UniversallyInjective (f.restrictScalars A)) :
    UniversallyInjective ((LocalizedModule.map S' f).restrictScalars A) := sorry

variable {N : Type w} [AddCommGroup N] [Module (Localization S') N]
variable {N' : Type x} [AddCommGroup N'] [Module (Localization S') N']

section

variable [Fact (S ≤ S'.comap (algebraMap A B))]

local instance localizationMapAlgebra : Algebra (Localization S) (Localization S') :=
  RingHom.toAlgebra
    (IsLocalization.map (Localization S') (algebraMap A B)
      (show S ≤ S'.comap (algebraMap A B) from Fact.out))

local instance localizedModuleModule : Module (Localization S) (LocalizedModule S' M) :=
  Module.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M)

local instance localizedModuleModule' : Module (Localization S) (LocalizedModule S' M') :=
  Module.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M')

local instance localizedModuleIsScalarTower :
    IsScalarTower (Localization S) (Localization S') (LocalizedModule S' M) :=
  IsScalarTower.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M)

local instance localizedModuleIsScalarTower' :
    IsScalarTower (Localization S) (Localization S') (LocalizedModule S' M') :=
  IsScalarTower.restrictScalars (Localization S) (Localization S') (LocalizedModule S' M')

/-- Lemma 10.82.12 (2): if a `B`-linear map is universally injective as a map of `A`-modules and
`S` maps into `S'`, then its localization at `S'` is universally injective as a map of
`A[S⁻¹]`-modules. -/
-- Proof sketch: first view `B[S'⁻¹]` as an `A[S⁻¹]`-algebra via the induced localization map
-- `A[S⁻¹] → B[S'⁻¹]`; then apply the same tensor-localization argument as in the `A`-linear case,
-- using the induced scalar tower on the localized modules.
theorem universallyInjective_localizedModule_over_localization
    (f : M →ₗ[B] M')
    (hf : UniversallyInjective (f.restrictScalars A)) :
    UniversallyInjective ((LocalizedModule.map S' f).restrictScalars (Localization S)) := sorry

/-- Lemma 10.82.12 (3): for `B[S'⁻¹]`-linear maps, universal injectivity over `A` is equivalent to
universal injectivity over `A[S⁻¹]`, where both scalar restrictions are the canonical ones induced
from the `B[S'⁻¹]`-module structure and `hSS'`. -/
-- Proof sketch: use that tensoring over `A` with an `A[S⁻¹]`-module is the same as tensoring
-- over `A[S⁻¹]`, and conversely that a `B[S'⁻¹]`-module already has all elements of `S`
-- acting invertibly, so tensoring over `A` factors through `A[S⁻¹]`.
theorem universallyInjective_iff_over_localization
    (f : N →ₗ[Localization S'] N') :
    by
      letI : Module A N := Module.restrictScalars A (Localization S') N
      letI : Module A N' := Module.restrictScalars A (Localization S') N'
      letI : IsScalarTower A (Localization S') N :=
        IsScalarTower.restrictScalars A (Localization S') N
      letI : IsScalarTower A (Localization S') N' :=
        IsScalarTower.restrictScalars A (Localization S') N'
      letI : Module (Localization S) N := Module.restrictScalars (Localization S) (Localization S') N
      letI : Module (Localization S) N' := Module.restrictScalars (Localization S) (Localization S') N'
      letI : IsScalarTower (Localization S) (Localization S') N :=
        IsScalarTower.restrictScalars (Localization S) (Localization S') N
      letI : IsScalarTower (Localization S) (Localization S') N' :=
        IsScalarTower.restrictScalars (Localization S) (Localization S') N'
      exact UniversallyInjective (f.restrictScalars A) ↔
        UniversallyInjective (f.restrictScalars (Localization S)) := sorry

end

end

end

end LinearMap
