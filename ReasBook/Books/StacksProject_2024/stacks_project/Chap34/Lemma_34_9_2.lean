import StacksProject_2024.Chap34.Definition_34_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine-open-cover owners in mathlib; local
-- Chapter 34 precedent fixes the fpqc-family owner at `IsFpqcCovering` on an indexed family
-- `ι → Over T`. The predicates below record the three source reformulations using quasi-compact
-- opens together with the canonical `T.AffineOpenCover` owner for affine open covers.

variable {T : Scheme.{u}} {ι : Type v}

/-- The affine-open quasi-compact image-cover criterion for an indexed family of schemes over `T`.
This is the source's condition that every affine open of `T` is the union of the images of an
almost-everywhere-empty family of quasi-compact opens in the members of the family. -/
def HasAffineOpenQuasiCompactImageCover (X : ι → Over T) : Prop :=
  (∀ i : ι, Flat (X i).hom) ∧
    ∀ U : T.Opens, IsAffineOpen U →
      ∃ V : (i : ι) → (X i).left.Opens,
        Set.Finite {i : ι | V i ≠ ⊥} ∧
          (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
            (⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)) = (U : Set T)

/-- A family satisfying the affine-open quasi-compact image-cover criterion is pointwise flat. -/
theorem HasAffineOpenQuasiCompactImageCover.flat
    {X : ι → Over T} (hX : HasAffineOpenQuasiCompactImageCover X) (i : ι) :
    Flat (X i).hom :=
  hX.1 i

/-- Source-facing projection of the affine-open quasi-compact image-cover criterion. -/
theorem HasAffineOpenQuasiCompactImageCover.exists_quasiCompact_image_cover
    {X : ι → Over T} (hX : HasAffineOpenQuasiCompactImageCover X)
    (U : T.Opens) (hU : IsAffineOpen U) :
    ∃ V : (i : ι) → (X i).left.Opens,
      Set.Finite {i : ι | V i ≠ ⊥} ∧
        (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
          (⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)) = (U : Set T) :=
  hX.2 U hU

/-- An affine-open-cover reformulation of the quasi-compact image-cover criterion for an indexed
family of schemes over `T`. -/
def HasAffineOpenCoverFiniteQuasiCompactImageRefinement (X : ι → Over T) : Prop :=
  (∀ i : ι, Flat (X i).hom) ∧
    ∃ 𝒰 : Scheme.AffineOpenCover.{v} T,
      ∀ a : 𝒰.I₀,
        ∃ V : (i : ι) → (X i).left.Opens,
          Set.Finite {i : ι | V i ≠ ⊥} ∧
            (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
              (⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)) =
                  (((𝒰.f a).opensRange) : Set T)

/-- A family satisfying the affine-open-cover finite quasi-compact image refinement criterion is
pointwise flat. -/
theorem HasAffineOpenCoverFiniteQuasiCompactImageRefinement.flat
    {X : ι → Over T} (hX : HasAffineOpenCoverFiniteQuasiCompactImageRefinement X) (i : ι) :
    Flat (X i).hom :=
  hX.1 i

/-- Source-facing projection of the affine-open-cover finite quasi-compact image refinement
criterion. -/
theorem HasAffineOpenCoverFiniteQuasiCompactImageRefinement.exists_affineOpenCover
    {X : ι → Over T} (hX : HasAffineOpenCoverFiniteQuasiCompactImageRefinement X) :
    ∃ 𝒰 : Scheme.AffineOpenCover.{v} T,
      ∀ a : 𝒰.I₀,
        ∃ V : (i : ι) → (X i).left.Opens,
          Set.Finite {i : ι | V i ≠ ⊥} ∧
            (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
              (⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)) =
                  (((𝒰.f a).opensRange) : Set T) :=
  hX.2

/-- A pointwise neighborhood reformulation of the quasi-compact image-cover criterion for an
indexed family of schemes over a quasi-separated target. -/
def HasPointwiseFiniteQuasiCompactNeighborhoodCover (X : ι → Over T) : Prop :=
  (∀ i : ι, Flat (X i).hom) ∧
    ∀ t : T,
      ∃ V : (i : ι) → (X i).left.Opens,
        Set.Finite {i : ι | V i ≠ ⊥} ∧
          (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
            ∃ W : T.Opens,
              t ∈ (W : Set T) ∧
                (W : Set T) ⊆
                  ⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left)

/-- A family satisfying the pointwise finite quasi-compact neighborhood criterion is pointwise
flat. -/
theorem HasPointwiseFiniteQuasiCompactNeighborhoodCover.flat
    {X : ι → Over T} (hX : HasPointwiseFiniteQuasiCompactNeighborhoodCover X) (i : ι) :
    Flat (X i).hom :=
  hX.1 i

/-- Source-facing projection of the pointwise finite quasi-compact neighborhood criterion. -/
theorem HasPointwiseFiniteQuasiCompactNeighborhoodCover.exists_neighborhood
    {X : ι → Over T} (hX : HasPointwiseFiniteQuasiCompactNeighborhoodCover X) (t : T) :
    ∃ V : (i : ι) → (X i).left.Opens,
      Set.Finite {i : ι | V i ≠ ⊥} ∧
        (∀ i : ι, IsCompact (V i : Set (X i).left)) ∧
          ∃ W : T.Opens,
            t ∈ (W : Set T) ∧
              (W : Set T) ⊆
                ⋃ i : ι, (X i).hom.base '' (V i : Set (X i).left) :=
  hX.2 t

/-- Lemma 34.9.2 (1): an indexed family of morphisms to a scheme `T` is an fpqc covering if and
only if each morphism is flat and every affine open of `T` is the union of the images of an
almost-everywhere-empty family of quasi-compact opens in the members of the family. -/
theorem isFpqcCovering_iff_hasAffineOpenQuasiCompactImageCover (X : ι → Over T) :
    IsFpqcCovering X ↔ HasAffineOpenQuasiCompactImageCover X := sorry

/-- Lemma 34.9.2 (2): the affine-open quasi-compact image-cover criterion is equivalent to requiring
only an affine open cover of the target together with finite quasi-compact image refinements on
each member of that cover. -/
theorem hasAffineOpenQuasiCompactImageCover_iff_hasAffineOpenCoverFiniteQuasiCompactImageRefinement
    (X : ι → Over T) :
    HasAffineOpenQuasiCompactImageCover X ↔
      HasAffineOpenCoverFiniteQuasiCompactImageRefinement X := sorry

/-- Lemma 34.9.2 (3): if `T` is quasi-separated, the affine-open quasi-compact image-cover
criterion is equivalent to the pointwise neighborhood criterion by finitely many quasi-compact
opens in the source family. -/
theorem hasAffineOpenQuasiCompactImageCover_iff_hasPointwiseFiniteQuasiCompactNeighborhoodCover
    (X : ι → Over T) [QuasiSeparatedSpace T] :
    HasAffineOpenQuasiCompactImageCover X ↔
      HasPointwiseFiniteQuasiCompactNeighborhoodCover X := sorry

end AlgebraicGeometry
