import Mathlib.Topology.CWComplex.Abstract.Basic
import Mathlib.Topology.Homotopy.Equiv

open scoped ContinuousMap

universe u

namespace TopCat

/-- A space `X` is of CW type if it is homotopy equivalent to some CW complex. -/
abbrev HasCWType (X : TopCat.{u}) : Prop :=
  ∃ Y : TopCat.{u}, Nonempty (CWComplex Y) ∧ Nonempty (X ≃ₕ Y)

/-- The defining existential form of `TopCat.HasCWType`. -/
theorem hasCWType_iff {X : TopCat.{u}} :
    HasCWType X ↔ ∃ Y : TopCat.{u}, Nonempty (CWComplex Y) ∧ Nonempty (X ≃ₕ Y) :=
  Iff.rfl

/-- A homotopy equivalence from `X` to a CW complex exhibits `X` as being of CW type. -/
theorem hasCWType_of_homotopyEquiv {X Y : TopCat.{u}} (hY : CWComplex Y) (e : X ≃ₕ Y) :
    HasCWType X :=
  ⟨Y, ⟨hY⟩, ⟨e⟩⟩

end TopCat
