import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Finite.Card
import Mathlib.Topology.CWComplex.Classical.Finite

open scoped BigOperators
open Topology

universe u

noncomputable section

/-- Euler characteristic of a finite CW complex, computed from the chosen finite CW structure as
the alternating `finsum` of the numbers of cells in each dimension. -/
noncomputable def cwEulerCharacteristic {X : Type u} [TopologicalSpace X] (C : Set X)
    [CWComplex C] [CWComplex.Finite C] : ℤ :=
  ∑ᶠ n : ℕ, (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n)

namespace Topology.CWComplex

/-- The CW Euler characteristic attached to an explicit finite CW structure on `C`. -/
noncomputable def eulerCharacteristic {X : Type u} [TopologicalSpace X] {C : Set X}
    (c : CWComplex C) (hfinite : letI : CWComplex C := c; CWComplex.Finite C) : ℤ :=
  letI : CWComplex C := c
  letI : CWComplex.Finite C := hfinite
  cwEulerCharacteristic C

@[inherit_doc cwEulerCharacteristic]
scoped notation "χ(" C ")" => _root_.cwEulerCharacteristic C

end Topology.CWComplex

open scoped Topology.CWComplex

@[simp] theorem cwEulerCharacteristic_def {X : Type u} [TopologicalSpace X] {C : Set X}
    [CWComplex C] [CWComplex.Finite C] :
    χ(C) = ∑ᶠ n : ℕ, (Int.negOnePow n : ℤ) * Nat.card (Topology.CWComplex.cell C n) :=
  rfl
