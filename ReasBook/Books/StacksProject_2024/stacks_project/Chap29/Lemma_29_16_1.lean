import Mathlib.AlgebraicGeometry.ResidueField
import StacksProject_2024.Chap29.Definition_29_15_1
import StacksProject_2024.Chap29.Definition_29_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

-- Semantic recall: mathlib's residue-field API supplies `Scheme.stalkClosedPointTo` and
-- `Scheme.descResidueField` for the residue-field map of a field-valued point; local Chapter 29
-- precedent uses `Scheme.Hom.FiniteType`, `Scheme.Hom.FiniteTypeAt`, and `IsFiniteTypePoint` for
-- the finite-type owners appearing in the source.

section

variable {S T : Scheme.{u}} {k : Type u} [Field k]

/-- The image in the target scheme of the unique closed point of `Spec(k)` under a field-valued
point `f`. -/
abbrev closedPointImage (f : Spec (CommRingCat.of k) ⟶ T) : T :=
  f (IsLocalRing.closedPoint k)

/-- The canonical algebra structure on `k` over the residue field of the image of the closed point
of `Spec(k)` under `f`. -/
instance closedPointImageResidueFieldAlgebra
    (f : Spec (CommRingCat.of k) ⟶ T) :
    Algebra (T.residueField (closedPointImage f)) k :=
  (CommRingCat.Hom.hom (Scheme.descResidueField (Scheme.stalkClosedPointTo f))).toAlgebra

/-- The residue-field extension induced by a field-valued point `f` is finite. -/
def HasFiniteResidueFieldExtension
    (f : Spec (CommRingCat.of k) ⟶ T) : Prop :=
  Module.Finite (T.residueField (closedPointImage f)) k

/-- Unfolding form of `HasFiniteResidueFieldExtension`. -/
theorem hasFiniteResidueFieldExtension_iff
    (f : Spec (CommRingCat.of k) ⟶ T) :
    HasFiniteResidueFieldExtension f ↔
      Module.Finite (T.residueField (closedPointImage f)) k :=
  Iff.rfl

/-- An affine-open factorization of a field-valued point whose induced coordinate-ring map is a
finite ring map. -/
def HasAffineOpenFiniteAppTopFactorization
    (f : Spec (CommRingCat.of k) ⟶ S) : Prop :=
      ∃ U : S.affineOpens,
    ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
      g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
        (CommRingCat.Hom.hom (appTop g)).Finite

/-- Unfolding form of `HasAffineOpenFiniteAppTopFactorization`. -/
theorem hasAffineOpenFiniteAppTopFactorization_iff
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasAffineOpenFiniteAppTopFactorization f ↔
      ∃ U : S.affineOpens,
        ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
          g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
            (CommRingCat.Hom.hom (appTop g)).Finite :=
  Iff.rfl

/-- An affine-open factorization of a field-valued point whose image is a closed point of that
affine open and whose induced residue-field extension is finite. -/
def HasAffineOpenClosedPointFiniteResidueExtension
    (f : Spec (CommRingCat.of k) ⟶ S) : Prop :=
  ∃ U : S.affineOpens,
    ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
      g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
        closedPointImage g ∈ closedPoints (S.restrict (U : S.Opens).isOpenEmbedding) ∧
          HasFiniteResidueFieldExtension g

/-- Unfolding form of `HasAffineOpenClosedPointFiniteResidueExtension`. -/
theorem hasAffineOpenClosedPointFiniteResidueExtension_iff
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasAffineOpenClosedPointFiniteResidueExtension f ↔
      ∃ U : S.affineOpens,
        ∃ g : Spec (CommRingCat.of k) ⟶ S.restrict (U : S.Opens).isOpenEmbedding,
          g ≫ S.ofRestrict (U : S.Opens).isOpenEmbedding = f ∧
            closedPointImage g ∈ closedPoints (S.restrict (U : S.Opens).isOpenEmbedding) ∧
              HasFiniteResidueFieldExtension g :=
  Iff.rfl

/-- Lemma 29.16.1 (1): for a field-valued point `f : Spec(k) ⟶ S`, being of finite type is
equivalent to being locally of finite type. -/
@[stacks 01TA]
theorem finiteType_iff_locallyOfFiniteType
    (f : Spec (CommRingCat.of k) ⟶ S) :
    FiniteType f ↔ LocallyOfFiniteType f := sorry

/-- Lemma 29.16.1 (2): for a field-valued point `f : Spec(k) ⟶ S`, being locally of finite type
is equivalent to admitting an affine-open factorization whose induced coordinate-ring map is
finite. -/
@[stacks 01TA]
theorem locallyOfFiniteType_iff_hasAffineOpenFiniteAppTopFactorization
    (f : Spec (CommRingCat.of k) ⟶ S) :
    LocallyOfFiniteType f ↔ HasAffineOpenFiniteAppTopFactorization f := sorry

/-- Lemma 29.16.1 (3): for a field-valued point `f : Spec(k) ⟶ S`, an affine-open factorization
with finite coordinate-ring map is equivalent to an affine-open factorization whose image is a
closed point and whose residue-field extension is finite. -/
@[stacks 01TA]
theorem hasAffineOpenFiniteAppTopFactorization_iff_hasAffineOpenClosedPointFiniteResidueExtension
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasAffineOpenFiniteAppTopFactorization f ↔
      HasAffineOpenClosedPointFiniteResidueExtension f := sorry

/-- Companion API: for a field-valued point, local finite type is exactly the pointwise finite-type
condition at the unique point of `Spec(k)`. -/
theorem locallyOfFiniteType_iff_finiteTypeAt_closedPoint
    (f : Spec (CommRingCat.of k) ⟶ S) :
    LocallyOfFiniteType f ↔ f.FiniteTypeAt (IsLocalRing.closedPoint k) := sorry

/-- Companion API: the source affine-open closed-point criterion is exactly that the image point of
`f` is a finite type point of `S` and the induced residue-field extension is finite. -/
theorem hasAffineOpenClosedPointFiniteResidueExtension_iff_image_isFiniteTypePoint_and_moduleFinite
    (f : Spec (CommRingCat.of k) ⟶ S) :
    HasAffineOpenClosedPointFiniteResidueExtension f ↔
      IsFiniteTypePoint (closedPointImage f) ∧
        HasFiniteResidueFieldExtension f := sorry

/-- Companion API: a field-valued point is of finite type exactly when its image point is a finite
type point of `S` and the induced residue-field extension is finite. -/
theorem finiteType_iff_image_isFiniteTypePoint_and_moduleFinite
    (f : Spec (CommRingCat.of k) ⟶ S) :
    FiniteType f ↔ IsFiniteTypePoint (closedPointImage f) ∧
      HasFiniteResidueFieldExtension f := sorry

end

end Scheme.Hom
end AlgebraicGeometry
