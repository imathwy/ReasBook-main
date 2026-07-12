import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall / local owner check:
-- - `lean_leansearch` surfaced the canonical dominant-morphism owner `AlgebraicGeometry.IsDominant`.
-- - Local Chapter 29 precedent already uses `genericPoint`, `Scheme.Hom.appLE`, and
--   `Scheme.Hom.stalkMap` for the generic-point, affine-open, and stalk formulations.
-- - Since the source is a six-way equivalence, the source-facing statement is packaged as a local
--   `List.TFAE`.

/-- A nonempty affine open of a scheme. -/
abbrev NonemptyAffineOpen (X : Scheme.{u}) : Type _ :=
  { U : X.affineOpens // Set.Nonempty (U : Set X) }

/-- Lemma 29.8.8: let `f : X ⟶ Y` be a morphism of integral schemes. Then the following are
equivalent: `f` is dominant, `f` maps the generic point of `X` to the generic point of `Y`, for
some nonempty affine opens `U ⊆ X` and `V ⊆ Y` with `f(U) ⊆ V` the induced ring map
`\Gamma(Y, V) → \Gamma(X, U)` is injective, for all such nonempty affine opens the induced ring
map is injective, for some `x : X` the local ring map `𝒪_{Y, f(x)} → 𝒪_{X, x}` is injective, and
for every `x : X` the local ring map `𝒪_{Y, f(x)} → 𝒪_{X, x}` is injective. -/
@[stacks 0CC1]
theorem isDominant_tfae_of_isIntegral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] :
    List.TFAE
      [ IsDominant f
      , f (genericPoint X) = genericPoint Y
      , ∃ U : NonemptyAffineOpen X, ∃ V : NonemptyAffineOpen Y,
            ∃ e :
                ((U.1 : X.affineOpens) : X.Opens) ≤
                  (TopologicalSpace.Opens.map f.base).obj ((V.1 : Y.affineOpens) : Y.Opens),
              Function.Injective
                (CommRingCat.Hom.hom
                  (Scheme.Hom.appLE f ((V.1 : Y.affineOpens) : Y.Opens)
                    ((U.1 : X.affineOpens) : X.Opens) e))
      , ∀ U : NonemptyAffineOpen X, ∀ V : NonemptyAffineOpen Y,
            ∀ e :
                ((U.1 : X.affineOpens) : X.Opens) ≤
                  (TopologicalSpace.Opens.map f.base).obj ((V.1 : Y.affineOpens) : Y.Opens),
              Function.Injective
                (CommRingCat.Hom.hom
                  (Scheme.Hom.appLE f ((V.1 : Y.affineOpens) : Y.Opens)
                    ((U.1 : X.affineOpens) : X.Opens) e))
      , ∃ x : X, Function.Injective (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f x))
      , ∀ x : X, Function.Injective (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f x))
      ] := sorry

end AlgebraicGeometry
