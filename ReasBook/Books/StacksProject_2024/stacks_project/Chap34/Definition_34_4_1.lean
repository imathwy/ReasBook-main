import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Definition_7_8_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: mathlib already provides the canonical big étale precoverage
-- `Scheme.etalePrecoverage`, and a covering family in Definition 34.4.1 is precisely a cover for
-- that owner.

/- Definition 34.4.1: the canonical owner for the big étale covering notion on schemes is
`Scheme.etalePrecoverage`. -/
recall Scheme.etalePrecoverage

/- Definition 34.4.1: an étale covering of a scheme is the canonical cover object
`Scheme.Cover Scheme.etalePrecoverage`, i.e. a jointly surjective family of étale morphisms to the
target. -/
#check Scheme.Cover Scheme.etalePrecoverage

namespace Cover

/-- The underlying fixed-target family attached to a scheme-site cover. -/
abbrev toFamilyOver {T : Scheme.{u}} {K : Precoverage Scheme.{u}} (𝒰 : T.Cover K) :
    SemiRepresentableFamily.Over T :=
  ofArrows 𝒰.X 𝒰.f

@[simp] theorem toFamilyOver_obj
    {T : Scheme.{u}} {K : Precoverage Scheme.{u}} (𝒰 : T.Cover K) (i : 𝒰.I₀) :
    𝒰.toFamilyOver.obj i = CategoryTheory.Over.mk (𝒰.f i) :=
  rfl

end Cover

end AlgebraicGeometry.Scheme
