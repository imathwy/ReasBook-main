import StacksProject_2024.stacks_project.Chap29.Definition_29_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall: `lean_leansearch` surfaced `LocallyQuasiFinite`, `IsFinite`, and the
restriction morphism `f ∣_ U`; local Chapter 29 precedent uses the Stacks-facing global owner
`Scheme.Hom.QuasiFinite` and expresses dense opens as `Dense (U : Set Y)`. The Stacks tag evidence
is consistent for tag `03HZ`. -/

/-- Remark 29.51.3: a quasi-finite morphism of schemes is finite over a dense open subset of
the target. -/
@[stacks 03HZ]
theorem exists_dense_open_isFinite_restrict_of_quasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiFinite f] :
    ∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (f ∣_ U) := sorry

end Scheme.Hom
end AlgebraicGeometry
