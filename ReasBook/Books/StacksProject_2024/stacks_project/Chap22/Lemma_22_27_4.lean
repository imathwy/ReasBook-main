import StacksProject_2024.Chap22.Situation_22_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable [CompBoundaryMap R A]

-- Semantic recall hit: `lean_leansearch` surfaced the concrete cochain-complex theorem
-- `CochainComplex.mappingCone.homotopyToZeroOfId`. In the current project context, the verified
-- local owner for this source item is `AdmissibleCone (𝟙 x)` from `Situation_22_27_2`; because the
-- local `Comp(𝒜)` API already packages homotopy canonically by `Homotopic`, so the faithful
-- public surface is the direct null-homotopy statement.

namespace AdmissibleCone

/-- Lemma 22.27.4: in Situation `22.27.2`, for any object `x` of `Comp(𝒜)` and any chosen cone on
the identity morphism `𝟙 x`, the identity morphism of the cone object is a boundary, i.e. it is
homotopic to zero in the sense of Lemma `22.26.5`. -/
@[stacks 09QK]
theorem id_homotopic_zero_of_id
    {x : Comp R A}
    (cone : AdmissibleCone (𝟙 x)) :
    Homotopic cone.obj.obj cone.obj.obj (CompHom.id cone.obj.obj) 0 := sorry

/-- Companion boundary form of Lemma `22.27.4`: the identity endomorphism of the cone object is
the differential of a degree-`-1` morphism. -/
theorem id_isBoundary_of_id
    {x : Comp R A}
    (cone : AdmissibleCone (𝟙 x)) :
    ∃ h : cone.obj.obj ⟶[-1] cone.obj.obj, D.id cone.obj.obj = D.d (-1) h := by
  rcases
      (CompHom.homotopic_zero_iff (CompHom.id cone.obj.obj)).mp
        (id_homotopic_zero_of_id cone) with
    ⟨h, hh⟩
  exact ⟨h, by simpa using hh⟩

end AdmissibleCone

end
