module

public import Topology_Munkres_2000.Book.Proposition_25_1.Instances
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Instances.RatLemmas

public section

universe u

/- Proposition 25.1 (1): every connected component of a space is closed. -/
#check isClosed_connectedComponent

/-- Helper for Proposition 25.1: if a space has finitely many connected components,
then each connected component is open. -/
theorem isOpen_connectedComponent_of_finite_components {X : Type u}
    [TopologicalSpace X] [Finite (ConnectedComponents X)] (x : X) :
    IsOpen (connectedComponent x) :=
  ConnectedComponents.discreteTopology_iff.mp inferInstance x

/-- Proposition 25.1: in general, a connected component need not be open. -/
theorem exists_connectedComponent_not_isOpen :
    ∃ (X : TopCat.{u}) (x : X), ¬ IsOpen (connectedComponent x) := by
  -- Lift `ℚ` to the required universe and transport its total disconnectedness.
  let rationalLiftHomeomorph : ULift.{u} ℚ ≃ₜ ℚ := Homeomorph.ulift
  letI : TotallyDisconnectedSpace (ULift.{u} ℚ) :=
    rationalLiftHomeomorph.symm.totallyDisconnectedSpace
  -- Use the lifted zero as a component whose singleton cannot be open.
  refine ⟨TopCat.of (ULift.{u} ℚ), ULift.up 0, ?_⟩
  -- Total disconnectedness identifies the component with the lifted singleton.
  rw [connectedComponent_eq_singleton]
  intro hOpen
  -- Openness would descend along the homeomorphism and isolate zero in `ℚ`.
  have hImage : rationalLiftHomeomorph '' {ULift.up (0 : ℚ)} = {0} := by
    rw [Set.image_singleton]
    rfl
  have hOpenZero : IsOpen ({0} : Set ℚ) := by
    rw [← hImage]
    exact rationalLiftHomeomorph.isOpen_image.mpr hOpen
  exact not_isOpen_singleton (0 : ℚ) hOpenZero
