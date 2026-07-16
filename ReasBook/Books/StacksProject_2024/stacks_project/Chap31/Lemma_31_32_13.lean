import StacksProject_2024.stacks_project.Chap28.Lemma_28_24_2
import StacksProject_2024.stacks_project.Chap29.Definition_29_43_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_37_4
import StacksProject_2024.stacks_project.Chap31.Definition_31_32_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X X' : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced absolute `Proj`, while local Chapter 29/31
-- inspection found the project morphism owner `Projective`, the relative-ampleness owner
-- `RelativelyAmple`, the relative-`Proj` twist family `Scheme.Hom.RelativeProjPresentation`,
-- and the blowup owner `IsBlowup`.

/-- The `n`-th power of a quasi-coherent ideal sheaf, expressed on affine opens by powers of the
corresponding section ideals. -/
abbrev idealSheafPower (I : X.IdealSheafData) (n : ℕ) : X.IdealSheafData :=
  Scheme.IdealSheafData.ofIdeals fun U ↦ I.ideal U ^ n

/-- On affine opens, `idealSheafPower I n` has section ideal `I(U)^n`. -/
theorem idealSheafPower_ideal (I : X.IdealSheafData) (n : ℕ) (U : X.affineOpens) :
    (idealSheafPower I n).ideal U = I.ideal U ^ n := sorry

/-- Lemma 31.32.13 (1): if `b : X' -> X` is the blowup of a scheme `X` in a finite type
quasi-coherent ideal sheaf `I`, then `b` is a projective morphism. -/
@[stacks 02NS]
theorem projective_of_isBlowup_finiteTypeIdeal
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [((Subobject.underlying.obj (idealSheafSubobject I) : X.Modules).IsFiniteType)] :
    Projective b := sorry

/-- Lemma 31.32.13 (2): for the Rees relative-`Proj` presentation of the blowup of `X` in a
finite type quasi-coherent ideal sheaf `I`, the twisting sheaf `O_{X'}(1)` is invertible and
`b`-relatively ample. The hypothesis `hP` records that the chosen relative-`Proj` presentation
has degree pieces `I^d`. -/
@[stacks 02NS]
theorem blowup_reesTwistOne_relativelyAmple
    (I : X.IdealSheafData) (b : X' ⟶ X) [IsBlowup b I]
    [((Subobject.underlying.obj (idealSheafSubobject I) : X.Modules).IsFiniteType)]
    (P : Scheme.Hom.RelativeProjPresentation b)
    (hP : ∀ n : ℕ,
      P.degreePiece n =
        (Subobject.underlying.obj (idealSheafSubobject (idealSheafPower I n)) : X.Modules)) :
    RelativelyAmple b (P.twist 1) := sorry

end

end AlgebraicGeometry
