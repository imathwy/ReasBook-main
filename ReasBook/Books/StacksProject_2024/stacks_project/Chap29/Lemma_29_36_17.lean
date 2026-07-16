import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_15
import StacksProject_2024.stacks_project.Chap29.Lemma_29_36_16

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced `AlgebraicGeometry.IsEtale.instIsStableUnderBaseChangeScheme`,
  `AlgebraicGeometry.IsEtale`, and the affine `Algebra.etaleLocus` API.
- Local Chapter 29 precedent fixes pointwise étaleness as `Scheme.Hom.EtaleAt` and records
  base-change loci as set preimages under the projection to the source.
- The source tag evidence is consistent: Stacks tag `0476` is the URL tag for
  `Lemma 29.36.17`.
-/

/-- Lemma 29.36.17 (1): in a cartesian square of schemes, let `W` and `W'` be the open
subschemes whose underlying sets are the points where `f` and `f'` are étale. If `f` is flat and
locally of finite presentation, then `W'` is the inverse image of `W` under `g'`. -/
@[stacks 0476]
theorem etaleLocusOpen_eq_preimage_of_isPullback_of_flat_locallyOfFinitePresentation
    {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    [Flat f] [LocallyOfFinitePresentation f] (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | f.EtaleAt x})
    (hW' : (W' : Set X') = {x' : X' | f'.EtaleAt x'}) :
    W' = g' ⁻¹ᵁ W := sorry

/-- Lemma 29.36.17 (2): in a cartesian square of schemes, let `W` and `W'` be the open
subschemes whose underlying sets are the points where `f` and `f'` are étale. If `f` is locally of
finite presentation and the base-change morphism `g` is flat, then `W'` is the inverse image of
`W` under `g'`. -/
@[stacks 0476]
theorem etaleLocusOpen_eq_preimage_of_isPullback_of_locallyOfFinitePresentation_base_flat
    {X S S' X' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    [LocallyOfFinitePresentation f] [Flat g] (W : X.Opens) (W' : X'.Opens)
    (hW : (W : Set X) = {x : X | f.EtaleAt x})
    (hW' : (W' : Set X') = {x' : X' | f'.EtaleAt x'}) :
    W' = g' ⁻¹ᵁ W := sorry

end AlgebraicGeometry
