import StacksProject_2024.stacks_project.Chap20.Definition_20_49_1
import StacksProject_2024.stacks_project.Chap20.«20_42_0_1»
import StacksProject_2024.stacks_project.Chap20.Open_subspace_module_core
import StacksProject_2024.stacks_project.Chap20.Tensor_internal_hom_to_iterated_internal_hom

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.50.4:
- primary domain: tensor/internal-Hom comparison morphisms in the braided monoidal closed derived
  category `D(𝒪_X)` of a ringed space, together with the perfectness owner on derived
  objects;
- sampled declarations:
  `tensorInternalHomToIteratedInternalHom`,
  `DerivedCategory.IsPerfect`,
  `SheafOfModules.RingedSite.isIso_curry_exactPairingEvaluation`,
  `CategoryTheory.ExactPairing`;
- best owner abstraction:
  `source-facing`: the ringed-space result below asserting that the canonical comparison morphism
    from Lemma `20.42.9` is an isomorphism for perfect `K`;
  `core/canonical`: the comparison morphism owner
    `tensorInternalHomToIteratedInternalHom K L M`, together with the monoidal duality owner
    `ExactPairing`;
  `bridge/view`: this result is the perfectness-to-isomorphism bridge that later feeds the
    canonical exact-pairing construction for the derived dual, while the sheaf-level exact-pairing
    comparison theorem remains a distinct upstream owner in the underived setting.
- primitive data: the ambient braided monoidal closed structure on `RingedSpaceDerived X`, the
  objects `K`, `L`, `M`, and the source-facing perfectness hypothesis `DerivedCategory.IsPerfect K`;
- derived API: the `IsIso` witness for `tensorInternalHomToIteratedInternalHom K L M`.

This file should therefore stay source-facing: it should reuse the existing comparison morphism
owner from Lemma `20.42.9` and the Chapter 20 perfectness owner directly, while avoiding any fresh
wrapper around the ambient derived category.
-/
section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]
variable [∀ U : Opens X.carrier, CategoryWithHomology (openSubspaceModuleCategory X U)]

local notation "DMod" => RingedSpaceDerived X

-- Proof sketch: work locally on `X` using compatibility of both sides with localization. Replace
-- the perfect object `K` by a strictly perfect representative, then argue by distinguished
-- triangles and stupid truncations to reduce to a finite free module sheaf in one degree, where
-- the comparison is the evident isomorphism.
/-- Lemma 20.50.4: let `(X, 𝒪_X)` be a ringed space and let `K`, `L`, `M ∈ D(𝒪_X)`. If `K` is
perfect, then the canonical map
`RHom(L, M) ⊗[𝒪_X]^L K ⟶ RHom(RHom(K, L), M)` from Lemma `20.42.9` is an isomorphism. -/
@[stacks 0G40]
instance isIso_tensorInternalHomToIteratedInternalHom_of_isPerfect
    {K L M : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (tensorInternalHomToIteratedInternalHom K L M) := sorry

end

end AlgebraicGeometry.RingedSpace
