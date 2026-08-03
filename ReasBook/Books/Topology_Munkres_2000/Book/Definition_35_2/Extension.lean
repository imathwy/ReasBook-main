module

public import Mathlib.Topology.TietzeExtension

public section

universe u v

/-- A space has the universal extension property when every continuous map from a closed
subspace of a normal space extends continuously to the whole space. Here `T4Space` expresses
the book's convention that normal spaces are also `T₁`. -/
class UniversalExtensionProperty (Y : Type v) [TopologicalSpace Y] : Prop where
  exists_restrict_eq {X : Type u} [TopologicalSpace X] [T4Space X] (A : Set X)
    (hA : IsClosed A) (f : C(A, Y)) : ∃ g : C(X, Y), g.restrict A = f

namespace TietzeExtension

/-- Mathlib's Tietze extension property implies the book's universal extension property. -/
instance universalExtensionProperty {Y : Type v} [TopologicalSpace Y]
    [TietzeExtension.{u, v} Y] : UniversalExtensionProperty.{u, v} Y where
  exists_restrict_eq _ hA f := f.exists_restrict_eq hA

end TietzeExtension
