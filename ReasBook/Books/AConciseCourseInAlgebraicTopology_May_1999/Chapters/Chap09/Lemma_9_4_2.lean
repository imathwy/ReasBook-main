import Mathlib.Topology.Homotopy.HomotopyGroup

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped unitInterval Topology Topology.Homotopy

variable {X : Type u} [TopologicalSpace X]

-- Semantic recall: `PreconnectedSpace.constant`, `GenLoop.const`, and `HomotopyGroup.Pi` are the
-- relevant mathlib APIs here.

private theorem genLoop_value_eq_basepoint_of_discrete [DiscreteTopology X] (n : ℕ) (x : X)
    (f : Ω^ (Fin (n + 1)) X x) (y : I^(Fin (n + 1))) :
    f y = x := by
  let zeroCube : I^(Fin (n + 1)) := fun _ ↦ 0
  have hp : PreconnectedSpace (I^(Fin (n + 1))) := inferInstance
  have hzeroCube : zeroCube ∈ Cube.boundary (Fin (n + 1)) := by
    exact ⟨0, Or.inl rfl⟩
  calc
    f y = f zeroCube :=
      hp.constant f.1.continuous
    _ = x := GenLoop.boundary f zeroCube hzeroCube

private theorem genLoop_eq_const_of_discrete [DiscreteTopology X] (n : ℕ) (x : X)
    (f : Ω^ (Fin (n + 1)) X x) :
    f = GenLoop.const := by
  ext y
  simpa using genLoop_value_eq_basepoint_of_discrete n x f y

private instance genLoopSubsingletonOfDiscrete [DiscreteTopology X] (n : ℕ) (x : X) :
    Subsingleton (Ω^ (Fin (n + 1)) X x) := by
  refine ⟨fun f g ↦ ?_⟩
  exact (genLoop_eq_const_of_discrete n x f).trans (genLoop_eq_const_of_discrete n x g).symm

/-- If `X` is discrete, then every positive-degree homotopy group `π_(n + 1) X x` is trivial. -/
instance homotopyGroupSubsingletonOfDiscrete [DiscreteTopology X] (n : ℕ) (x : X) :
    Subsingleton (π_ (n + 1) X x) := by
  refine ⟨fun a b ↦ Quotient.inductionOn₂ a b ?_⟩
  intro f g
  exact Quotient.sound <| by rw [Subsingleton.elim f g]

/-- Lemma 9.4.2: if `X` is discrete, then `π_ n X x` is trivial for every basepoint `x : X`
and every `n > 0`. -/
theorem homotopyGroup_subsingleton_of_discrete [DiscreteTopology X] (n : ℕ) (hn : 0 < n) (x : X) :
    Subsingleton (π_ n X x) := by
  rcases Nat.exists_eq_succ_of_ne_zero hn.ne' with ⟨m, rfl⟩
  infer_instance
