import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace Functor

section

variable {𝒟 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒟] [Category.{v₂} 𝒟']
  (S : MorphismProperty 𝒟) (F : 𝒟 ⥤ 𝒟')

/- Domain-style sampling for Lemma 13.14.4:
- primary domain: transport of pointwise left/right derived-definedness along morphisms in the
  localization class, together with the resulting isomorphism statements on the total derived
  functors;
- sampled owner declarations:
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `MorphismProperty.Q_inverts`,
  `MorphismProperty.IsInvertedBy.of_comp`,
  `Functor.totalRightDerived`,
  `Functor.totalLeftDerived`;
- best owner abstraction: the primitive owner data are the pointwise-definedness predicates
  `Functor.HasPointwiseRightDerivedFunctorAt` and `Functor.HasPointwiseLeftDerivedFunctorAt`, so
  the exact transport clauses should be direct recalls of the corresponding owner theorems; for
  the induced-isomorphism clauses, the owner-level abstraction is that the composite functors
  `S.Q ⋙ F.totalRightDerived S.Q S` and `S.Q ⋙ F.totalLeftDerived S.Q S` invert `S`, and the
  pointwise isomorphism statements should be thin companions derived from that owner fact;
- primitive data: a morphism `s` in `S` and the pointwise/global derived-functor existence
  owners;
- derived API: the owner-level inversion predicates for the composite total derived functors and
  the resulting isomorphism statements for the induced maps.

Source/core/bridge triage:
- `source-facing`: the four textbook clauses of Lemma 13.14.4;
- `core/canonical`: `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`, and the owner predicate
  `MorphismProperty.IsInvertedBy`;
- `bridge/view`: the two `Functor.total...Derived_map_isIso_of_mem` theorems below, which
  unpack the owner-level inversion statement into the source-facing pointwise isomorphism form.
-/

-- Proof sketch: this is exactly the invariance of pointwise right derived functors under
-- isomorphism in the localization, applied to the canonical isomorphism `Localization.isoOfHom`
-- attached to a morphism `s ∈ S`.
/- Lemma 13.14.4 (1): for a morphism `s : X ⟶ Y` in `S`, the right derived functor of `F`
is defined at `X` if and only if it is defined at `Y`. This is exactly the canonical owner
theorem for transport along a denominator. -/
recall hasPointwiseRightDerivedFunctorAt_iff_of_mem
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) {X Y : 𝒟} (s : X ⟶ Y) (hs : S s) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      F.HasPointwiseRightDerivedFunctorAt S Y

-- Proof sketch: a globally pointwise-defined right derived functor is a functor on the
-- localization `S.Localization`; since `S.Q.map s` is an isomorphism there, its image under the
-- total right derived functor is again an isomorphism.
/-- The composite `S.Q ⋙ RF` inverts every morphism of `S`. -/
theorem totalRightDerived_isInvertedBy [F.HasPointwiseRightDerivedFunctor S] :
    S.IsInvertedBy (S.Q ⋙ F.totalRightDerived S.Q S) :=
  MorphismProperty.IsInvertedBy.of_comp S S.Q S.Q_inverts (F.totalRightDerived S.Q S)

/-- Lemma 13.14.4 (2): if the right derived functor of `F` with respect to `S` is everywhere
defined, then the induced map on the values at `X` and `Y` coming from `s` is an isomorphism. -/
theorem totalRightDerived_map_isIso_of_mem {X Y : 𝒟} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseRightDerivedFunctor S] :
    IsIso ((F.totalRightDerived S.Q S).map (S.Q.map s)) := by
  simpa using totalRightDerived_isInvertedBy S F s hs

-- Proof sketch: this is the left-derived dual of the first clause, using the corresponding
-- invariance of pointwise left derived functors under isomorphism in the localization.
/- Lemma 13.14.4 (3): for a morphism `s : X ⟶ Y` in `S`, the left derived functor of `F`
is defined at `X` if and only if it is defined at `Y`. This is exactly the canonical owner
theorem for transport along a denominator. -/
recall hasPointwiseLeftDerivedFunctorAt_iff_of_mem
    (F : 𝒟 ⥤ 𝒟') (S : MorphismProperty 𝒟) {X Y : 𝒟} (s : X ⟶ Y) (hs : S s) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      F.HasPointwiseLeftDerivedFunctorAt S Y

-- Proof sketch: a globally pointwise-defined left derived functor is a functor on the
-- localization `S.Localization`; the morphism `S.Q.map s` is an isomorphism, so its image under
-- the total left derived functor is an isomorphism as well.
/-- The composite `S.Q ⋙ LF` inverts every morphism of `S`. -/
theorem totalLeftDerived_isInvertedBy [F.HasPointwiseLeftDerivedFunctor S] :
    S.IsInvertedBy (S.Q ⋙ F.totalLeftDerived S.Q S) :=
  MorphismProperty.IsInvertedBy.of_comp S S.Q S.Q_inverts (F.totalLeftDerived S.Q S)

/-- Lemma 13.14.4 (4): if the left derived functor of `F` with respect to `S` is everywhere
defined, then the induced map on the values at `X` and `Y` coming from `s` is an isomorphism. -/
theorem totalLeftDerived_map_isIso_of_mem {X Y : 𝒟} (s : X ⟶ Y) (hs : S s)
    [F.HasPointwiseLeftDerivedFunctor S] :
    IsIso ((F.totalLeftDerived S.Q S).map (S.Q.map s)) := by
  simpa using totalLeftDerived_isInvertedBy S F s hs

end

end Functor

end CategoryTheory
