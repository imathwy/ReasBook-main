import Mathlib
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap28.Lemma_28_13_8
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `UniversallyClosed`,
-- `ValuativeCriterion.Existence`, and `UniversallyClosed.of_valuativeCriterion`. Local Chapter 32
-- precedent uses `pullback.snd f (AffineSpace (Fin n) Y ↘ Y)` for the affine-space base-change
-- test, while local Chapter 28/29 precedent supplies `Scheme.Nagata`, `Scheme.isNormal`,
-- `Scheme.Hom.FiniteType`, `closedPoints`, and `ringKrullDim` for the Nagata one-dimensional
-- normal-curve test.

/-- The Nagata-base one-dimensional normal-curve lifting condition from Lemma 32.17.1.
For every diagram over `S` with `C` normal integral and finite type over `S`, with
`U = C \ {c}` for a closed point whose local ring has dimension `1`, and with a compatible
map `U ⟶ X`, the induced valuative square over `Spec(𝒪_{C,c})` admits a dotted lift.

The field `K` represents the fraction field of `𝒪_{C,c}`; the hypothesis `genericToU` and
`hgeneric` record that the generic point of `Spec(𝒪_{C,c})` lands in the punctured open `U`. -/
@[stacks 0GWV]
def NagataCurveValuativeExistence
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) : Prop :=
  ∀ (C : Scheme.{u}) (pC : C ⟶ S) [Scheme.Hom.FiniteType pC] [IsIntegral C],
    C.isNormal →
    ∀ (c : C), c ∈ closedPoints C → ringKrullDim (C.presheaf.stalk c) = 1 →
      ∀ (U : C.Opens), (U : Set C) = ({c} : Set C)ᶜ →
        ∀ (toX : U.toScheme ⟶ X) (toY : C ⟶ Y),
          toX ≫ f = U.ι ≫ toY →
          toX ≫ pX = U.ι ≫ pC →
          toY ≫ pY = pC →
          ∀ (K : Type u) [Field K] [Algebra (C.presheaf.stalk c) K]
            [IsFractionRing (C.presheaf.stalk c) K],
              ∀ (genericToU : Spec (CommRingCat.of K) ⟶ U.toScheme),
                genericToU ≫ U.ι =
                    Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk c) K)) ≫
                      C.fromSpecStalk c →
                  ∀ sq : CommSq (genericToU ≫ toX)
                    (Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk c) K)))
                    f (C.fromSpecStalk c ≫ toY),
                      sq.HasLift

/-- Unfolding companion for `NagataCurveValuativeExistence`. -/
@[stacks 0GWV]
theorem nagataCurveValuativeExistence_iff
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) :
    NagataCurveValuativeExistence pX pY f ↔
      ∀ (C : Scheme.{u}) (pC : C ⟶ S) [Scheme.Hom.FiniteType pC] [IsIntegral C],
        C.isNormal →
        ∀ (c : C), c ∈ closedPoints C → ringKrullDim (C.presheaf.stalk c) = 1 →
          ∀ (U : C.Opens), (U : Set C) = ({c} : Set C)ᶜ →
            ∀ (toX : U.toScheme ⟶ X) (toY : C ⟶ Y),
              toX ≫ f = U.ι ≫ toY →
              toX ≫ pX = U.ι ≫ pC →
              toY ≫ pY = pC →
              ∀ (K : Type u) [Field K] [Algebra (C.presheaf.stalk c) K]
                [IsFractionRing (C.presheaf.stalk c) K],
                  ∀ (genericToU : Spec (CommRingCat.of K) ⟶ U.toScheme),
                    genericToU ≫ U.ι =
                        Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk c) K)) ≫
                          C.fromSpecStalk c →
                      ∀ sq : CommSq (genericToU ≫ toX)
                        (Spec.map (CommRingCat.ofHom (algebraMap (C.presheaf.stalk c) K)))
                        f (C.fromSpecStalk c ≫ toY),
                          sq.HasLift := sorry

/-- Lemma 32.17.1: let `S` be a Nagata scheme and let `f : X ⟶ Y` be a quasi-compact morphism
of schemes locally of finite type over `S`. Then the following are equivalent: `f` is universally
closed; for every `n`, the base change
`\mathbf A^n_Y ×_Y X ⟶ \mathbf A^n_Y` is a closed map; and the one-dimensional normal-curve
valuative lifting condition over `S` holds. -/
@[stacks 0GWV]
theorem universallyClosed_tfae_affineSpace_closed_nagataCurveValuative
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    [Scheme.Nagata S] [QuasiCompact f] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (hf_over : f ≫ pY = pX) :
    List.TFAE
      [ UniversallyClosed f
      , ∀ n : ℕ, IsClosedMap (pullback.snd f (AffineSpace (Fin n) Y ↘ Y)).base
      , NagataCurveValuativeExistence pX pY f
      ] := sorry

end AlgebraicGeometry
