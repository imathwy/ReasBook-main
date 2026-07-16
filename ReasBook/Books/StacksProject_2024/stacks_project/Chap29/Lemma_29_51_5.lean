import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
`LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`, `IsFinite`, and the restriction
API `f ∣_ V`; local Chapter 29 precedent uses `genericPointsOfIrreducibleComponents`
for the source notation `X⁰` and `Y⁰`. The source tag evidence is consistent for tag
`0BAI`. -/

/-- Lemma 29.51.5: if a locally finite type morphism `f : X ⟶ Y` carries exactly the generic
points of irreducible components of `X` over those of `Y`, the two sets of such generic points are
finite, and `f` is either quasi-compact or separated, then `f` is finite over a dense open subset
of the target. -/
@[stacks 0BAI]
theorem exists_dense_open_isFinite_restrict_of_preimage_genericPointsOfIrreducibleComponents_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hX : (genericPointsOfIrreducibleComponents X).Finite)
    (hY : (genericPointsOfIrreducibleComponents Y).Finite)
    (hpreimage : f.base ⁻¹' genericPointsOfIrreducibleComponents Y =
      genericPointsOfIrreducibleComponents X)
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f) :
    ∃ V : Y.Opens, Dense (V : Set Y) ∧ IsFinite (f ∣_ V) := sorry

end Scheme.Hom
end AlgebraicGeometry
