module

public import Mathlib.Topology.LocallyFinite

public section

universe u v

/-- An indexed family of subsets is point-finite when each point belongs to only
finitely many members of the family. -/
def PointFinite {ι : Type u} {X : Type v} (A : ι → Set X) : Prop :=
  ∀ x : X, {i | x ∈ A i}.Finite

/-- Point-finiteness is exactly finiteness of the set of indices containing each point. -/
theorem pointFinite_iff {ι : Type u} {X : Type v} {A : ι → Set X} :
    PointFinite A ↔ ∀ x : X, {i | x ∈ A i}.Finite := Iff.rfl

namespace PointFinite

/-- At a chosen point, a point-finite family has only finitely many containing members. -/
theorem finite {ι : Type u} {X : Type v} {A : ι → Set X}
    (hA : PointFinite A) (x : X) : {i | x ∈ A i}.Finite := hA x

end PointFinite

namespace LocallyFinite

/-- Every locally finite indexed family of subsets is point-finite. -/
theorem toPointFinite {ι : Type u} {X : Type v} [TopologicalSpace X]
    {A : ι → Set X} (hA : LocallyFinite A) : PointFinite A := hA.point_finite

end LocallyFinite
