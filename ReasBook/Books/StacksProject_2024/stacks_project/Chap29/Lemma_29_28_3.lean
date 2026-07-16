import StacksProject_2024.stacks_project.Chap05.Definition_5_10_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_28_4
-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Semantic recall / owner check:
- local Chapter 29 precedent packages the local fiber dimension at a point by the canonical owner
  `Scheme.Hom.fiberDimensionAt`;
- `Lemma_29_28_1` already identifies that owner with the source-facing topological view
  `topologicalKrullDimAt (f.asFiber x)`.
-/

namespace Scheme.Hom

section

variable {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
  (g' : X' ⟶ X) (f' : X' ⟶ S') (hpb : IsPullback g' f' f g)

/-- Lemma 29.28.3 (1) in owner form: local fiber dimension is preserved by pullback. -/
theorem fiberDimensionAt_eq_of_isPullback
    (x' : X') :
    f'.fiberDimensionAt x' = f.fiberDimensionAt (g' x') := sorry

end

section

variable {S X S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)

/-- The canonical pullback-square specialization of Lemma 29.28.3 (1) for the owner
`Scheme.Hom.fiberDimensionAt`. -/
theorem fiberDimensionAt_eq_of_pullback_snd
    (x' : pullback f g) :
    (pullback.snd f g).fiberDimensionAt x' = f.fiberDimensionAt (pullback.fst f g x') := sorry

/-- The same pullback-square specialization in the source-facing topological-fiber language. -/
theorem topologicalKrullDimAt_asFiber_eq_of_pullback_snd
    (x' : pullback f g) :
    topologicalKrullDimAt ((pullback.snd f g).asFiber x') =
      topologicalKrullDimAt (f.asFiber (pullback.fst f g x')) := sorry

end

end Scheme.Hom

section

variable {S X S' X' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
  (g' : X' ⟶ X) (f' : X' ⟶ S') (hpb : IsPullback g' f' f g)

/-- The canonical `κ(f(g'(x')))`-algebra structure on `κ(g'(x'))` induced by `f`. -/
local instance sourceResidueFieldAlgebraAtPoint (x' : X') :
    Algebra (S.residueField (f (g' x'))) (X.residueField (g' x')) :=
  (f.residueFieldMap (g' x')).hom.toAlgebra

/-- The canonical `κ(f'(x'))`-algebra structure on `κ(x')` induced by `f'`. -/
local instance pullbackResidueFieldAlgebraAtPoint (x' : X') :
    Algebra (S'.residueField (f' x')) (X'.residueField x') :=
  (f'.residueFieldMap x').hom.toAlgebra

local notation "sourceFiberStalk" =>
  fun x' : X' ↦ ((f.fiber (f (g' x'))).presheaf.stalk (f.asFiber (g' x')))

local notation "baseChangeFiberStalk" =>
  fun x' : X' ↦ ((g'.fiber (g' x')).presheaf.stalk (g'.asFiber x'))

local notation "pullbackFiberStalk" =>
  fun x' : X' ↦ ((f'.fiber (f' x')).presheaf.stalk (f'.asFiber x'))

local notation "sourceFiberStalkAt" =>
  fun x : X ↦ ((f.fiber (f x)).presheaf.stalk (f.asFiber x))

/-- The canonical `κ(f(x))`-algebra structure on `κ(x)` induced by `f`. -/
local instance sourceResidueFieldAlgebraAtSourcePoint (x : X) :
    Algebra (S.residueField (f x)) (X.residueField x) :=
  (f.residueFieldMap x).hom.toAlgebra

local notation "sourceTrdeg" =>
  fun x' : X' ↦
    Cardinal.toNat
      (Algebra.trdeg
        (S.residueField (f (g' x')))
        (X.residueField (g' x')))

local notation "sourceTrdegAt" =>
  fun x : X ↦
    Cardinal.toNat
      (Algebra.trdeg
        (S.residueField (f x))
        (X.residueField x))

local notation "pullbackTrdeg" =>
  fun x' : X' ↦
    Cardinal.toNat
      (Algebra.trdeg
        (S'.residueField (f' x'))
        (X'.residueField x'))

-- Semantic recall note: the scheme-fiber owner/API choice is fixed here by
-- `Chap05/Definition_5_10_1.lean`, `Chap29/Definition_29_28_4.lean`, and the flat base-change
-- precedent in `Chap29/Lemma_29_25_7.lean`.

/-- Lemma 29.28.3 (1): for a locally finite type morphism `f : X ⟶ S`, a base change
`g : S' ⟶ S`, a pullback square `X' ⟶ X` over `S' ⟶ S`, and a point `x' : X'`, the local
dimensions of the fibers of `f'` at `x'` and of `f` at the image `g'(x')` agree. This is the
source-facing topological companion to `Scheme.Hom.fiberDimensionAt_eq_of_isPullback`. -/
@[stacks 02FY "(1)"]
theorem topologicalKrullDimAt_asFiber_eq_of_isPullback
    (x' : X') :
    topologicalKrullDimAt (f'.asFiber x') =
      topologicalKrullDimAt (f.asFiber (g' x')) := sorry

/-- Lemma 29.28.3 (2): in the same pullback situation, the local ring dimension of the fiber of
`g'` over `g'(x')`, equivalently the fiber of `X'_{f'(x')}` over `g'(x')`, plus the local ring
dimension of the fiber of `f` at `g'(x')`, equals the local ring dimension of the fiber of `f'`
at `x'`. This is the additive form of the source's difference formula. -/
@[stacks 02FY "(2)"]
theorem ringKrullDim_stalk_fiber_eq_sub_fiberStalkDim_of_isPullback
    (x' : X') :
    ringKrullDim (sourceFiberStalk x') + ringKrullDim (baseChangeFiberStalk x') =
      ringKrullDim (pullbackFiberStalk x') := sorry

/-- Lemma 29.28.3 (3): the same fiber-local dimension is the difference between the transcendence
degrees `trdeg_{κ(s)} κ(x)` and `trdeg_{κ(s')} κ(x')` attached to the corresponding points of
`X`, `S`, `X'`, and `S'`. -/
@[stacks 02FY "(3)"]
theorem ringKrullDim_stalk_fiber_eq_trdeg_sub_of_isPullback
    (x' : X') :
    ringKrullDim (baseChangeFiberStalk x') = sourceTrdeg x' - pullbackTrdeg x' := sorry

/-- Lemma 29.28.3 (4): base change does not decrease the local ring dimension of the fiber at the
corresponding point. -/
@[stacks 02FY "(4)"]
theorem ringKrullDim_stalk_fiber_le_of_isPullback
    (x' : X') :
    ringKrullDim (sourceFiberStalk x') ≤ ringKrullDim (pullbackFiberStalk x') := sorry

/-- Lemma 29.28.3 (5): under the same base change, the transcendence degree of the residue field
extension at the image point in `X` is at least the transcendence degree at `x'`. -/
@[stacks 02FY "(5)"]
theorem trdeg_residueField_le_of_isPullback
    (x' : X') :
    pullbackTrdeg x' ≤ sourceTrdeg x' := sorry

/-- Lemma 29.28.3 (6): for `s' : S'` and `x : X` with `f x = g s'`, one can choose a point
`x' : X'` over `x` and `s'` in the pullback square such that both the image equalities and the
pair of numerical equalities from the source hold. -/
@[stacks 02FY "(6)"]
theorem exists_point_with_fiberStalkDim_eq_and_trdeg_eq_of_isPullback
    (s' : S') (x : X) (hxs : f x = g s') :
    ∃ x' : X',
      g' x' = x ∧
        f' x' = s' ∧
        ringKrullDim (pullbackFiberStalk x') = ringKrullDim (sourceFiberStalkAt x) ∧
        pullbackTrdeg x' = sourceTrdegAt x := sorry

end

end AlgebraicGeometry
