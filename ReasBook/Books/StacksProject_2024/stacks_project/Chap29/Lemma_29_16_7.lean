import Mathlib
import StacksProject_2024.Chap29.Definition_29_16_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

/- Semantic recall: `lean_leansearch` surfaced the topological owners `IsLocallyClosed` and
`Dense`, and local Chapter 29 precedent fixes finite type points as `finiteTypePoints S`. -/

/-- Lemma 29.16.7 (1): every nonempty locally closed subset of a scheme meets the set of
finite type points. -/
@[stacks 02J4]
theorem finiteTypePoints_inter_nonempty_of_isLocallyClosed
    (S : Scheme.{u}) {T : Set S} (hT : IsLocallyClosed T) (hne : T.Nonempty) :
    (T ∩ finiteTypePoints S).Nonempty := sorry

/-- Lemma 29.16.7 (2): for a closed subset `T` of a scheme `S`, the points of finite type in
`S` are dense in `T`, with `T` carrying its subtype topology. -/
@[stacks 02J4]
theorem dense_finiteTypePoints_in_closed_subset
    (S : Scheme.{u}) {T : Set S} (hT : IsClosed T) :
    Dense {x : T | (x : S) ∈ finiteTypePoints S} := sorry

end AlgebraicGeometry
