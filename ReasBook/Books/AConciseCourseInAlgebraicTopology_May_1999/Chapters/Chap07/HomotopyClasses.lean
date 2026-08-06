import Mathlib.Topology.Homotopy.Path

open scoped ContinuousMap

noncomputable section

universe u

/-- The setoid on `C(X, Y)` given by ordinary homotopy. -/
def continuousMapHomotopySetoid (X Y : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] : Setoid C(X, Y) where
  r := ContinuousMap.Homotopic
  iseqv := ContinuousMap.Homotopic.equivalence

/-- The quotient of `C(X, Y)` by ordinary homotopy. -/
abbrev continuousMapHomotopyClasses (X Y : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] :=
  Quotient (continuousMapHomotopySetoid X Y)

/-- Postcomposition by a continuous map descends to homotopy classes of continuous maps. -/
def continuousMapHomotopyClassesPostcompose {X Y Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (g : C(Y, Z)) :
    continuousMapHomotopyClasses X Y → continuousMapHomotopyClasses X Z :=
  Quotient.map
    (fun f : C(X, Y) ↦ g.comp f)
    (fun _ _ h ↦ ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl g) h)

/-- Precomposition by a continuous map descends to homotopy classes of continuous maps. -/
def continuousMapHomotopyClassesPrecompose {X Y Z : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X, Y)) :
    continuousMapHomotopyClasses Y Z → continuousMapHomotopyClasses X Z :=
  Quotient.map
    (fun g : C(Y, Z) ↦ g.comp f)
    (fun _ _ h ↦ ContinuousMap.Homotopic.comp h (ContinuousMap.Homotopic.refl f))
