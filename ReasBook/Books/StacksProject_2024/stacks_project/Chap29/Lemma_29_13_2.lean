import StacksProject_2024.stacks_project.Chap29.Definition_29_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` found the canonical owners
`Scheme.instIsSeparatedOfIsQuasiAffine`, `QuasiCompact`, and `Scheme.IsQuasiAffine.of_isAffineHom`.
Combined with the local `QuasiAffineHom` abbreviation from Definition 29.13.1, the source-facing
API here is the two morphism-property consequences `IsSeparated f` and `QuasiCompact f`. -/

/-- Lemma 29.13.2 (1): a quasi-affine morphism is separated. -/
theorem QuasiAffineHom.isSeparated
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : QuasiAffineHom f) :
    IsSeparated f := sorry

/-- Lemma 29.13.2 (2): a quasi-affine morphism is quasi-compact. -/
theorem QuasiAffineHom.quasiCompact
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : QuasiAffineHom f) :
    QuasiCompact f := sorry

end AlgebraicGeometry
