import StacksProject_2024.Chap31.Definition_31_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: Chapter 31 already owns the absolute immersion predicates
-- `IsQuasiRegularImmersion` and `IsH1RegularImmersion`; Definition 31.22.2 only adds the
-- relative flatness condition on the structural composite `Z ⟶ S`.

section

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- Definition 31.22.2 (1): an immersion `i : Z ⟶ X` over `f : X ⟶ S` is a relative
quasi-regular immersion if `Z ⟶ S` is flat and `i` is a quasi-regular immersion. -/
@[stacks 063S, mk_iff]
class RelativeQuasiRegularImmersion (f : X ⟶ S) (i : Z ⟶ X)
    : Prop extends IsQuasiRegularImmersion i, Flat (i ≫ f)

/-- Definition 31.22.2 (2): an immersion `i : Z ⟶ X` over `f : X ⟶ S` is a relative
`H_1`-regular immersion if `Z ⟶ S` is flat and `i` is an `H_1`-regular immersion. -/
@[stacks 063S, mk_iff]
class RelativeH1RegularImmersion (f : X ⟶ S) (i : Z ⟶ X)
    : Prop extends IsH1RegularImmersion i, Flat (i ≫ f)

end

end AlgebraicGeometry
