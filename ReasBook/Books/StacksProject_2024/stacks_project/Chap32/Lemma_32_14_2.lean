import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]

-- Semantic recall: `lean_leansearch` surfaced the canonical owner `UniversallyClosed`,
-- the bridge `universallyClosed_iff`, and the closed-map theorem `Scheme.Hom.isClosedMap`;
-- local Chapter 29/32 precedent states base changes as the pullback projection `pullback.snd`
-- and relative affine space as `AffineSpace (Fin n) S` with projection `↘ S`.

/-- Lemma 32.14.2 (1): for a quasi-compact morphism of schemes, universal closedness is
equivalent to closedness of every base change by a morphism locally of finite presentation. -/
@[stacks 05JX]
theorem universallyClosed_iff_isClosedMap_lfp_baseChange :
    UniversallyClosed f ↔
      ∀ ⦃S' : Scheme.{u}⦄ (g : S' ⟶ S), LocallyOfFinitePresentation g →
        IsClosedMap (pullback.snd f g).base := sorry

/-- Lemma 32.14.2 (2): for a quasi-compact morphism of schemes, universal closedness is
equivalent to closedness after base change along every relative affine space
`\mathbf A^n_S ⟶ S`, i.e. for the morphisms
`\mathbf A^n_S ×_S X ⟶ \mathbf A^n_S`. -/
@[stacks 05JX]
theorem universallyClosed_iff_isClosedMap_affineSpace_baseChange :
    UniversallyClosed f ↔
      ∀ n : ℕ, IsClosedMap (pullback.snd f (AffineSpace (Fin n) S ↘ S)).base := sorry

end

end AlgebraicGeometry
