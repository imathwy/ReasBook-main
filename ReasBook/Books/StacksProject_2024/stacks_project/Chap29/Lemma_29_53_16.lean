import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_53_15

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

open Scheme.Hom

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical DVR owner `IsDiscreteValuationRing`. Local Chapter 29
-- precedent represents the relative normalization of `X` in `Y` as `f.normalization`, the map
-- `Y ⟶ f.normalization` as `f.toNormalization`, and scheme-theoretic fibres as `f.fiber x`.

/-- Auxiliary domain statement for the stalk appearing in Lemma 29.53.16; this supplies the
implicit domain argument required by mathlib's `IsDiscreteValuationRing` predicate. -/
theorem Scheme.Hom.isDomain_stalk_normalization_of_empty_fiber
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [LocallyOfFiniteType f]
    [IsReduced Y] [Scheme.Nagata X] (x' : normalization f)
    (hdim : ringKrullDim ((normalization f).presheaf.stalk x') = 1)
    (hfiber : IsEmpty (fiber (toNormalization f) x')) :
    IsDomain ((normalization f).presheaf.stalk x') := sorry

/-- Lemma 29.53.16: let `f : Y ⟶ X` be a finite type morphism of schemes with `Y` reduced and
`X` Nagata. Let `X'` be the normalization of `X` in `Y`. If `x' : X'` has
`dim(𝒪_{X', x'}) = 1` and the fibre of `Y ⟶ X'` over `x'` is empty, then `𝒪_{X', x'}`
is a discrete valuation ring. -/
@[stacks 0BXB]
theorem Scheme.Hom.isDiscreteValuationRing_stalk_normalization_of_empty_fiber
    {Y X : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [LocallyOfFiniteType f]
    [IsReduced Y] [Scheme.Nagata X] (x' : normalization f)
    (hdim : ringKrullDim ((normalization f).presheaf.stalk x') = 1)
    (hfiber : IsEmpty (fiber (toNormalization f) x')) :
    @IsDiscreteValuationRing
      ((normalization f).presheaf.stalk x') inferInstance
      (isDomain_stalk_normalization_of_empty_fiber f x' hdim hfiber) := sorry

end AlgebraicGeometry
