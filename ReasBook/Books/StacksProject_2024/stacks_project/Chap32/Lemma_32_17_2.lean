import Mathlib
import StacksProject_2024.Chap32.Lemma_32_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `IsSeparated.valuativeCriterion`, `IsSeparated.of_valuativeCriterion`, and
-- `ValuativeCriterion.Uniqueness`. Local Chapter 32 precedent represents the Nagata-base
-- one-dimensional normal-curve test through `C.fromSpecStalk c`, `Spec.map`, and
-- `CommSq.LiftStruct`.

/-- The Nagata-base one-dimensional normal-curve uniqueness condition from Lemma 32.17.2.
For every diagram over `S` with `C` normal integral and finite type over `S`, with
`U = C \ {c}` for a closed point whose local ring has dimension `1`, the induced valuative
square over `Spec(𝒪_{C,c})` has at most one dotted lift. -/
@[stacks 0GWW]
def NagataCurveValuativeUniqueness
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
                      Subsingleton sq.LiftStruct

/-- Unfolding companion for `NagataCurveValuativeUniqueness`. -/
@[stacks 0GWW]
theorem nagataCurveValuativeUniqueness_iff
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y) :
    NagataCurveValuativeUniqueness pX pY f ↔
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
                          Subsingleton sq.LiftStruct := sorry

/-- Lemma 32.17.2: let `S` be a Nagata scheme and let `f : X ⟶ Y` be a morphism of schemes
locally of finite type over `S`. Then `f` is separated if and only if the Nagata-base
one-dimensional normal-curve valuative uniqueness condition over `S` holds. -/
@[stacks 0GWW]
theorem isSeparated_iff_nagataCurveValuativeUniqueness
    {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
    [Scheme.Nagata S] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    (hf_over : f ≫ pY = pX) :
    IsSeparated f ↔ NagataCurveValuativeUniqueness pX pY f := sorry

end AlgebraicGeometry
