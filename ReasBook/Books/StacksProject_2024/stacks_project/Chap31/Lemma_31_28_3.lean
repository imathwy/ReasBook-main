import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.pullback` and
-- `Scheme.Modules.restrictFunctor` as the canonical module restriction owners. Local
-- Chapter 31 precedent for Lemma 31.28.2 uses `U.toScheme`, `U.ι`, and the stalkwise hypothesis
-- `UniqueFactorizationMonoid (X.presheaf.stalk x)` for points outside the open.

/-- Lemma 31.28.3: let `X` be a locally Noetherian scheme, let `U ⊆ X` be an open
subscheme, and let `ℒ` be an invertible `\mathcal O_U`-module. If every local ring
`\mathcal O_{X,x}` at a point of `X \ U` is a unique factorization domain, then `ℒ` extends to
an invertible `\mathcal O_X`-module. -/
@[stacks 0BD9]
theorem exists_invertibleModule_extension_of_stalks_uniqueFactorizationMonoid
    {X : Scheme.{u}} [IsLocallyNoetherian X] [MonoidalCategory X.Modules]
    (U : X.Opens) [MonoidalCategory U.toScheme.Modules]
    (ℒ : U.toScheme.Modules) [Functor.IsEquivalence (tensorRight ℒ)]
    (hUFD : ∀ x : X, x ∉ (U : Set X) → UniqueFactorizationMonoid (X.presheaf.stalk x)) :
    ∃ ℒ' : X.Modules,
      Functor.IsEquivalence (tensorRight ℒ') ∧
        Nonempty (ℒ ≅ ((Scheme.Modules.pullback U.ι).obj ℒ')) := sorry

end AlgebraicGeometry.Scheme
