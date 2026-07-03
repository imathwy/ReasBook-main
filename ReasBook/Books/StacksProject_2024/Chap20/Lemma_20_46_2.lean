import Mathlib
import StacksProject_2024.Chap20.Definition_20_46_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CochainComplex

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable {K L : CochainComplex (RingedSpace.Modules X) ℤ}

-- Proof sketch: unpack `IsStrictlyPerfect`. Boundedness of the mapping cone follows
-- from boundedness of `K` and `L`, and each term of `mappingCone f` is a binary
-- biproduct of a term of `L` with a shifted term of `K`, so the termwise retract presentations by
-- finite free modules combine to give one for the cone term.
/-- Lemma 20.46.2: the cone of a morphism between strictly perfect complexes of
`\mathcal O_X`-modules is strictly perfect. -/
theorem mappingCone_isStrictlyPerfect (f : K ⟶ L)
    (hK : CochainComplex.IsStrictlyPerfect K)
    (hL : CochainComplex.IsStrictlyPerfect L) :
    CochainComplex.IsStrictlyPerfect (mappingCone f) := sorry

end AlgebraicGeometry.RingedSpace
