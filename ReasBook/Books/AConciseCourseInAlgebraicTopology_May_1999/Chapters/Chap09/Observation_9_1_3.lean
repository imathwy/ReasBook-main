import Mathlib.Topology.Homotopy.HomotopyGroup

open scoped Topology Topology.Homotopy

universe u

variable (n : ℕ) {X : Type u} [TopologicalSpace X] (x : X)

-- Semantic recall via `lean_leansearch`: there is no single mathlib theorem for Observation 9.1.3;
-- the canonical surface is the trio `genLoopEquivOfUnique`, `GenLoop.genLoopGenLoopEquiv`, and
-- `HomotopyGroup.pi0EquivZerothHomotopy`.

/- Observation 9.1.3: mathlib models `π_ n X x` using generalized loops indexed by `Fin n`.
`genLoopEquivOfUnique` identifies singleton-indexed generalized loops with the ordinary loop space
`Ω X x`, `GenLoop.genLoopGenLoopEquiv` reassociates iterated generalized loops, and
`HomotopyGroup.pi0EquivZerothHomotopy` identifies `π_ 0` of an iterated loop space with its
zeroth homotopy set. Iterating the first two equivalences gives the textbook reduction of
`π_ n X x` to `π_ 0 (Ω^ (Fin n) X x)`. -/
#check (genLoopEquivOfUnique (Fin 1) : Ω^ (Fin 1) X x ≃ Ω X x)
#check
  (GenLoop.genLoopGenLoopEquiv x :
    Ω^ (Fin 1) (Ω^ (Fin n) X x) GenLoop.const ≃ₜ Ω^ (Fin 1 ⊕ Fin n) X x)
#check
  (HomotopyGroup.pi0EquivZerothHomotopy :
    π_ 0 (Ω^ (Fin n) X x) GenLoop.const ≃ ZerothHomotopy (Ω^ (Fin n) X x))
