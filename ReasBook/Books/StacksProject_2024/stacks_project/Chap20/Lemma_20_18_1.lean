import StacksProject_2024.Chap17.Definition_17_20_1
import StacksProject_2024.Chap20.Lemma_20_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open DerivedCategory.TStructure
open RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

private theorem pointInclusion_pullback_commSq
    {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y) [HasPullback f (pointInclusion y)] :
    CommSq
      (pullback.fst f (pointInclusion y))
      (pullback.snd f (pointInclusion y))
      f
      (pointInclusion y) := by
  exact CommSq.mk <| by
    simpa using
      (pullback.condition :
        pullback.fst f (pointInclusion y) ≫ f =
          pullback.snd f (pointInclusion y) ≫ pointInclusion y)

/-
Domain-style sampling for Lemma 20.18.1:
- primary domain: bounded-below derived pullback/pushforward for sheaves of `𝒪_X`-modules
  on a point-inclusion pullback square of ringed spaces;
- sampled owner declarations:
  `RingedSpace.IsBoundedBelowFlatBaseChangeMap`,
  `RingedSpace.Hom.IsFlat`,
  `pointInclusion_isFlat`,
  `pointInclusion`;
- best owner abstraction: the bounded-below flat base-change owner
  `RingedSpace.IsBoundedBelowFlatBaseChangeMap` from `Lemma_20_17_1`; this theorem is the
  `bridge/view` specialization asserting that any owner-level base-change morphism is an
  isomorphism for the square cut out by `pointInclusion y`;
- primitive data: the morphism `f : X ⟶ Y`, the point `y : Y`, the point inclusion
  `i : pointRingedSpace y ⟶ Y`, the pullback square `pullback f i`, and the underived pushforward
  and pullback functors on module sheaves;
- derived API: the specialized canonical source and target objects
  `i^* Rf_* E` and `R(f')_* (g')^* E`, together with the source-facing base-change-map
  specification from `Lemma_20_17_1`.

Source/core/bridge triage:
- `source-facing`: the stalk/fiber comparison of Lemma 20.18.1;
- `core/canonical`: `RingedSpace.IsBoundedBelowFlatBaseChangeMap`;
- `bridge/view`: the point-inclusion specialization of that owner predicate from `Lemma_20_17_1`.
-/

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y) (y : Y)

local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => D⁺(ModX)
local notation "iy" => pointInclusion y
local notation "g'" => pullback.fst f iy
local notation "f'" => pullback.snd f iy
local notation "sq" => pointInclusion_pullback_commSq f y

variable [HasPullback f (pointInclusion y)]

-- Proof sketch: specialize the base-change comparison of Lemma `20.17.1` to the cartesian square
-- obtained by pulling `f` back along the point inclusion `({y}, 𝒪_{Y, y}) ⟶ Y`. The
-- resulting pullback object models the fiber `f^{-1}(y)`, and the source hypotheses on `f`
-- identify the owner-level point-inclusion specialization with the usual stalk/fiber comparison.
/-
Lemma 20.18.1: if `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` is a closed and separated
morphism of ringed spaces, `y : Y`, and the fiber `f^{-1}(y)` is quasi-compact, then for every
bounded-below derived object `E : D⁺(ModX)` any bounded-below base-change morphism from
`i_y^* Rf_* E` to `R(f')_* (g')^* E` in the point-inclusion pullback square is an isomorphism.
This source-facing item is implemented through the canonical point-inclusion specialization of the
unique bounded-below base-change morphism from Lemma `20.17.1`. -/
@[stacks 09V5]
instance pointInclusion_boundedBelowFlatBaseChangeMap_isIso
    (hclosed : IsClosedMap f.hom.base)
    (hseparated : IsSeparatedMap f.hom.base)
    (hyqc : IsCompact (f.hom.base ⁻¹' ({y} : Set Y)))
    (E : DModX)
    (η : boundedBelowDerivedBaseChangeSource f iy E ⟶ boundedBelowFlatBaseChangeTarget g' f' E)
    (hη : IsBoundedBelowFlatBaseChangeMap g' f' f iy sq E η) : IsIso η := by
  sorry

end

end AlgebraicGeometry.RingedSpace
