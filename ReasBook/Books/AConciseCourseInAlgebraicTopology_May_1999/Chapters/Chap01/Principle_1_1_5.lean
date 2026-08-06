import Mathlib.Topology.Homotopy.TopCat.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- Principle 1.1.5: the usual strict form of the invariance principle says that an
algebraic-topological invariant is homotopy invariant when homotopic maps induce the same
morphism on the associated algebraic data. -/
class IsHomotopyInvariant (A : TopCat ⥤ C) : Prop where
  /-- A homotopy-invariant algebraic-topological invariant sends homotopic maps to the same
  induced morphism. -/
  map_eq {X Y : TopCat} {p q : X ⟶ Y} (H : TopCat.Homotopy p q) : A.map p = A.map q

/-- A homotopy-invariant algebraic-topological invariant sends homotopic maps to the same
induced morphism. -/
theorem map_eq_of_homotopy
    {A : TopCat ⥤ C} [A.IsHomotopyInvariant] {X Y : TopCat}
    {p q : X ⟶ Y} (H : TopCat.Homotopy p q) :
    A.map p = A.map q :=
  IsHomotopyInvariant.map_eq H

/-- A homotopy-invariant algebraic-topological invariant sends homotopic maps to the same
induced morphism. -/
theorem map_eq_of_homotopic
    {A : TopCat ⥤ C} [A.IsHomotopyInvariant] {X Y : TopCat}
    {p q : X ⟶ Y} (H : ContinuousMap.Homotopic p.hom q.hom) :
    A.map p = A.map q := by
  obtain ⟨H⟩ := H
  exact map_eq_of_homotopy H

end CategoryTheory.Functor
