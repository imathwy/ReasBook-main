import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `IsProper` and `isProper_iff` as the canonical
-- properness owner/API. Nearby Chapter 32 precedent represents base changes by `pullback.snd`
-- and the affine-space tests by `AffineSpace (Fin n) S ↘ S`.

/-- Lemma 32.14.3: let `S` be a scheme and let `f : X ⟶ S` be a separated morphism of finite
type. The following are equivalent: `f` is proper; every base change of `f` along a locally
finite type morphism `S' ⟶ S` is closed; and for every `n ≥ 0`, the base change of `f` along
`\mathbf A^n_S ⟶ S` is closed. -/
@[stacks 0205]
theorem isProper_tfae_isClosedMap_lft_baseChange_affineSpace
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] [Scheme.Hom.FiniteType f] :
    List.TFAE
      [ IsProper f
      , ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFiniteType g →
          IsClosedMap (pullback.snd f g).base
      , ∀ n : ℕ, IsClosedMap (pullback.snd f (AffineSpace (Fin n) S ↘ S)).base
      ] := sorry

end AlgebraicGeometry
