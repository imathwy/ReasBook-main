module

public import Topology_Munkres_2000.Book.Definition_66_1.WindingNumber
public import Mathlib.Topology.Connected.Basic

public section

open Set

namespace PlaneLoop

/-- A plane loop is counterclockwise when its winding number is `1` at some point in a bounded
connected component of its complement. Definition 66.4 applies this predicate to simple loops. -/
def IsCounterclockwise {x : ℂ} (f : Path x x) : Prop :=
  ∃ (a : ℂ) (h_avoid : a ∉ Set.range f),
    Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a) ∧
      windingNumber f a h_avoid = 1

/-- A plane loop is clockwise when its winding number is `-1` at some point in a bounded connected
component of its complement. Definition 66.4 applies this predicate to simple loops. -/
def IsClockwise {x : ℂ} (f : Path x x) : Prop :=
  ∃ (a : ℂ) (h_avoid : a ∉ Set.range f),
    Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a) ∧
      windingNumber f a h_avoid = -1

/-- Counterclockwise orientation is characterized by a bounded complementary component with
winding number `1`. -/
theorem isCounterclockwise_iff {x : ℂ} (f : Path x x) :
    IsCounterclockwise f ↔
      ∃ (a : ℂ) (h_avoid : a ∉ Set.range f),
        Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a) ∧
          windingNumber f a h_avoid = 1 := Iff.rfl

/-- Clockwise orientation is characterized by a bounded complementary component with winding
number `-1`. -/
theorem isClockwise_iff {x : ℂ} (f : Path x x) :
    IsClockwise f ↔
      ∃ (a : ℂ) (h_avoid : a ∉ Set.range f),
        Bornology.IsBounded (connectedComponentIn (Set.range f)ᶜ a) ∧
          windingNumber f a h_avoid = -1 := Iff.rfl

end PlaneLoop
