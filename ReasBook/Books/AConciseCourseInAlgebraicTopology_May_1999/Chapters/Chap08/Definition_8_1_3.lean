import Mathlib.Tactic.Recall
import Mathlib.Topology.ContinuousMap.ContinuousMapZero

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped ContinuousMapZero

variable {X : Type u} {Y : Type v} [Zero X] [Zero Y] [TopologicalSpace X] [TopologicalSpace Y]

-- Semantic recall: mathlib models based maps between spaces with distinguished points `0`
-- by `ContinuousMapZero`, written `C(X, Y)₀`.

/- Definition 8.1.3: the based mapping space `F(X, Y)` is the canonical type `C(X, Y)₀` of
continuous maps sending the basepoint `0 : X` to the basepoint `0 : Y`; its distinguished point
is `0`, the constant based map. -/
recall ContinuousMapZero (X : Type u) (Y : Type v) [Zero X] [Zero Y]
    [TopologicalSpace X] [TopologicalSpace Y] : Type (max u v)

notation "F(" X ", " Y ")" => C(X, Y)₀

/-- The distinguished basepoint of `F(X, Y)` is the constant based map at `0 : Y`. -/
@[simp] theorem basedMappingSpace_zero_eq_const :
    ((0 : F(X, Y)) : C(X, Y)) = ContinuousMap.const X (0 : Y) :=
  by
    ext x
    rfl
