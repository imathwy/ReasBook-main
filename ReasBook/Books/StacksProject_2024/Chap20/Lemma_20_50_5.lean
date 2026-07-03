import Mathlib
import StacksProject_2024.Chap20.Definition_20_49_1
import StacksProject_2024.Chap20.Lemma_20_42_8

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- The canonical bidual morphism `K ⟶ (K^∨)^∨` in `D(\mathcal O_X)`, obtained by currying the
evaluation map `K^∨ ⊗ K ⟶ \mathcal O_X`. -/
noncomputable def ringedSpaceDerivedBidualMap
    (K : DMod) :
    K ⟶ ringedSpaceDerivedDual (ringedSpaceDerivedDual K) :=
  MonoidalClosed.curry
    ((β_ (ringedSpaceDerivedDual K) K).hom ≫
      MonoidalClosed.uncurry (𝟙 (ringedSpaceDerivedDual K)))

-- Proof sketch: work locally on `X` and replace `K` by a strictly perfect representative. The
-- termwise dual complex is again strictly perfect, hence represents the derived dual, so the dual
-- object is perfect locally and therefore perfect.
/-- Lemma 20.50.5 (1): if `K` is a perfect object of `D(\mathcal O_X)`, then its derived dual
`K^∨ = R\mathcal H\!\mathit{om}(K, \mathcal O_X)` is perfect. -/
theorem isPerfect_derivedDual_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect (ringedSpaceDerivedDual K) := sorry

-- Proof sketch: apply Lemma `20.50.4` with `L = \mathcal O_X` and `M = \mathcal O_X` to see that
-- the tensor-to-iterated-internal-Hom comparison for `K` is an isomorphism. Under the
-- tensor-internal-Hom adjunction, this comparison is exactly the canonical bidual morphism.
/-- Lemma 20.50.5 (2): if `K` is a perfect object of `D(\mathcal O_X)`, then the canonical
bidual morphism `K ⟶ (K^∨)^∨` is an isomorphism, so `(K^∨)^∨` is canonically isomorphic to
`K`. -/
theorem isIso_ringedSpaceDerivedBidualMap_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedBidualMap K) := sorry

-- Proof sketch: this is exactly Lemma `20.50.4` specialized to `L = \mathcal O_X`, since
-- `K^∨ = R\mathcal H\!\mathit{om}(K, \mathcal O_X)` and
-- `M ⊗_{\mathcal O_X}^{\mathbf L} K^∨ ⟶ R\mathcal H\!\mathit{om}(K, M)` is the canonical map of
-- Lemma `20.42.8`.
/-- Lemma 20.50.5 (3): if `K` is a perfect object of `D(\mathcal O_X)`, then for every
`M ∈ D(\mathcal O_X)` the canonical morphism
`M \otimes_{\mathcal O_X}^{\mathbf L} K^∨ ⟶ R\mathcal H\!\mathit{om}(K, M)` is an
isomorphism. -/
theorem isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect
    {K M : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedEvaluationHom K M) := sorry

-- Proof sketch: the map on `H^0(X, -)` is induced by the canonical morphism of part `(3)`. Since
-- that morphism is an isomorphism for perfect `K`, taking degree-zero global sections gives a
-- bijection with `Hom_{D(\mathcal O_X)}(K, M)`.
/-- Lemma 20.50.5 (4): if `K` is a perfect object of `D(\mathcal O_X)`, then for every
`M ∈ D(\mathcal O_X)` the canonical map
`H^0(X, M \otimes_{\mathcal O_X}^{\mathbf L} K^∨) \to \operatorname{Hom}_{D(\mathcal O_X)}(K, M)`
is bijective. In Lean, `H^0(X, -)` is modeled by morphisms from the monoidal unit
`\mathcal O_X`. -/
theorem bijective_ringedSpaceDerivedEvaluationH0ToHom_of_isPerfect
    {K M : DMod} (hK : DerivedCategory.IsPerfect K) :
    Function.Bijective (ringedSpaceDerivedEvaluationH0ToHom K M) := sorry

end

end AlgebraicGeometry.RingedSpace
