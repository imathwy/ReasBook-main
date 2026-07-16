import Mathlib.Data.List.TFAE
import StacksProject_2024.stacks_project.Chap10.Definition_10_135_1
import StacksProject_2024.stacks_project.Chap23.Definition_23_8_5
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` was attempted for the scheme-side local complete-intersection owner but the
  endpoint returned HTTP 429;
- nearby project precedent uses `Over (Spec (CommRingCat.of k))` for schemes over a field and
  uses the canonical local-ring owner `IsCompleteIntersectionLocalRing` for complete-intersection
  stalk conditions;
- Chapter 29 already fixes the scheme-over-field owner as
  `IsLocalCompleteIntersectionOver k X.hom`, while Chapter 10 provides the affine algebra owners
  `IsLocalCompleteIntersection` and `IsGlobalCompleteIntersection`, and Chapter 23 provides the
  local-ring owner `IsCompleteIntersectionLocalRing`; the affine-neighbourhood formulations here
  are therefore companion statements around the existing scheme-level owner rather than new root
  predicates.
-/

section

variable {k : Type u} [Field k]

/-- A scheme over the field `k`, presented canonically as an object of `Over (Spec k)`. -/
abbrev SchemeOverField (k : Type u) [Field k] :=
  Over (Spec (CommRingCat.of k))

/-- The affine open neighbourhood of a point of a scheme over `Spec k`, viewed again as a scheme
over `Spec k` via the restricted structure morphism. -/
abbrev affineNeighborhoodOver
    (X : SchemeOverField k) (U : X.left.affineOpens) :
    SchemeOverField k :=
  Over.mk ((X.left.ofRestrict (U : X.left.Opens).isOpenEmbedding) ≫ X.hom)

/-- The affine `k`-scheme `Spec R`, regarded as an object of schemes over `Spec k`. -/
abbrev specOfAlgebraOver (R : Type u) [CommRing R] [Algebra k R] :
    SchemeOverField k :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R)))

/-- An affine open of a scheme over `Spec k` is a local complete-intersection neighbourhood over
`Spec k` if it is isomorphic, over `Spec k`, to the spectrum of a local complete-intersection
`k`-algebra. -/
def AffineOpenIsLocalCompleteIntersectionOver
    (X : SchemeOverField k) (U : X.left.affineOpens) : Prop :=
  ∃ (R : Type u) [CommRing R] [Algebra k R],
    IsLocalCompleteIntersection k R ∧
      Nonempty (affineNeighborhoodOver X U ≅ specOfAlgebraOver R)

/-- An affine open of a scheme over `Spec k` is a global complete-intersection neighbourhood over
`Spec k` if it is isomorphic, over `Spec k`, to the spectrum of a global complete-intersection
`k`-algebra. -/
def AffineOpenIsGlobalCompleteIntersectionOver
    (X : SchemeOverField k) (U : X.left.affineOpens) : Prop :=
  ∃ (R : Type u) [CommRing R] [Algebra k R],
    IsGlobalCompleteIntersection k R ∧
      Nonempty (affineNeighborhoodOver X U ≅ specOfAlgebraOver R)

/-- A global complete-intersection affine neighbourhood is, canonically, a local complete-
intersection affine neighbourhood. -/
theorem AffineOpenIsGlobalCompleteIntersectionOver.to_local
    {X : SchemeOverField k} {U : X.left.affineOpens}
    (hU : AffineOpenIsGlobalCompleteIntersectionOver X U) :
    AffineOpenIsLocalCompleteIntersectionOver X U := sorry

/-- A point of a scheme over `Spec k` has an affine local complete-intersection neighbourhood if it
lies in an affine open neighbourhood which, over `Spec k`, is isomorphic to the spectrum of a
local complete-intersection `k`-algebra. -/
def HasAffineLocalCompleteIntersectionNeighborhood
    (X : SchemeOverField k) (x : X.left) : Prop :=
  ∃ U : X.left.affineOpens, x ∈ (U : X.left.Opens) ∧
    AffineOpenIsLocalCompleteIntersectionOver X U

/-- A scheme over `Spec k` has affine local complete-intersection neighbourhoods if every point
admits one. -/
def HasAffineLocalCompleteIntersectionNeighborhoods
    (X : SchemeOverField k) : Prop :=
  ∀ x : X.left, HasAffineLocalCompleteIntersectionNeighborhood X x

/-- A scheme over `Spec k` is a local complete intersection exactly when every point admits an
affine open neighborhood whose structural morphism is, over `Spec k`, isomorphic to the spectrum
of a local complete-intersection `k`-algebra. -/
theorem isLocalCompleteIntersectionOver_iff_hasAffineLocalCompleteIntersectionNeighborhoods
    (X : SchemeOverField k) :
    IsLocalCompleteIntersectionOver k X.hom ↔
      HasAffineLocalCompleteIntersectionNeighborhoods X := sorry

/-- A point of a scheme over `Spec k` has an affine global complete-intersection neighbourhood if
it lies in an affine open neighbourhood which, over `Spec k`, is isomorphic to the spectrum of a
global complete-intersection `k`-algebra. -/
def HasAffineGlobalCompleteIntersectionNeighborhood
    (X : SchemeOverField k) (x : X.left) : Prop :=
  ∃ U : X.left.affineOpens, x ∈ (U : X.left.Opens) ∧
    AffineOpenIsGlobalCompleteIntersectionOver X U

/-- A point with an affine global complete-intersection neighbourhood has, canonically, an affine
local complete-intersection neighbourhood. -/
theorem HasAffineGlobalCompleteIntersectionNeighborhood.to_local
    {X : SchemeOverField k} {x : X.left}
    (hx : HasAffineGlobalCompleteIntersectionNeighborhood X x) :
    HasAffineLocalCompleteIntersectionNeighborhood X x := sorry

/-- A scheme over a field has affine global-complete-intersection neighbourhoods if every point
admits an affine open neighbourhood which, over `Spec k`, is isomorphic to the spectrum of a
global complete-intersection `k`-algebra. -/
def HasAffineGlobalCompleteIntersectionNeighborhoods
    (X : SchemeOverField k) : Prop :=
  ∀ x : X.left, HasAffineGlobalCompleteIntersectionNeighborhood X x

/-- Affine global complete-intersection neighbourhoods refine pointwise to affine local complete-
intersection neighbourhoods. -/
theorem HasAffineGlobalCompleteIntersectionNeighborhoods.to_local
    {X : SchemeOverField k}
    (hX : HasAffineGlobalCompleteIntersectionNeighborhoods X) :
    HasAffineLocalCompleteIntersectionNeighborhoods X := sorry

/-- Every local ring of `X` is a complete-intersection local ring. -/
def HasCompleteIntersectionStalks (X : Scheme.{u}) : Prop :=
  ∀ x : X, IsCompleteIntersectionLocalRing (X.presheaf.stalk x)

/-- Lemma 29.30.9: for a scheme `X` locally of finite type over a field `k`, the following are
equivalent: `X` is a local complete intersection over `k`; every point of `X` admits an affine
open neighbourhood over `k` whose coordinate ring is a global complete intersection over `k`; and
every local ring `𝒪_{X,x}` is a complete-intersection local ring. -/
theorem localCompleteIntersectionOverField_tfae
    (X : SchemeOverField k) [LocallyOfFiniteType X.hom] :
    List.TFAE
      [ IsLocalCompleteIntersectionOver k X.hom
      , HasAffineGlobalCompleteIntersectionNeighborhoods X
      , HasCompleteIntersectionStalks X.left
      ] := sorry

end

end AlgebraicGeometry
