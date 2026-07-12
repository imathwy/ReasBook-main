import StacksProject_2024.Chap34.Definition_34_8_4
import StacksProject_2024.Chap34.Definition_34_10_1

open CategoryTheory

universe u

namespace AlgebraicGeometry

namespace StandardPhCovering

section

variable {T : Scheme.{u}} [IsAffine T]

-- Semantic recall: `lean_leansearch` surfaced the affine-cover owners in mathlib, and local
-- Chapter 34 precedent packages standard `V` coverings as `AffineFamilyOver T` together with
-- `AffineFamilyOver.IsStandardVCover`. The source-facing bridge here is therefore the concrete
-- finite affine family underlying a `StandardPhCovering`.

/-- The finite affine family over the base scheme underlying a standard ph covering. -/
def toAffineFamily (Φ : StandardPhCovering T) : AffineFamilyOver T where
  n := Φ.m
  U := Φ.obj
  map := Φ.map
  isAffine := by
    intro j
    change IsAffine (((Φ.cover j : Φ.source.Opens)).toScheme)
    infer_instance

/-- The `j`-th morphism in the affine family underlying a standard ph covering is the original
component map. -/
@[simp] theorem toAffineFamily_map (Φ : StandardPhCovering T) (j : Fin Φ.m) :
    (toAffineFamily Φ).map j = Φ.map j :=
  rfl

/-- Lemma 34.10.3: the finite affine family underlying a standard ph covering is a standard `V`
covering. -/
@[stacks 0ETD]
theorem isStandardVCover (Φ : StandardPhCovering T) :
    AffineFamilyOver.IsStandardVCover (toAffineFamily Φ) := sorry

/-- The affine family underlying a standard ph covering is a standard `V` covering. -/
instance instIsStandardVCoverToAffineFamily (Φ : StandardPhCovering T) :
    AffineFamilyOver.IsStandardVCover (toAffineFamily Φ) :=
  isStandardVCover Φ

end

end StandardPhCovering

end AlgebraicGeometry
