import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 2.8.5: a topological space is simply connected when it is path connected and its
fundamental group is trivial; the canonical mathlib owner for this notion is
`SimplyConnectedSpace`. -/
recall SimplyConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

variable {X : Type u} [TopologicalSpace X]

namespace SimplyConnectedSpace

variable [SimplyConnectedSpace X]

/-- In a simply connected space, the fundamental group at every basepoint is trivial. -/
instance subsingletonFundamentalGroup (x : X) : Subsingleton (FundamentalGroup X x) := by
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

end SimplyConnectedSpace

/-- A simply connected space is path connected and has trivial fundamental group at every
basepoint. -/
theorem simplyConnectedSpace_iff_pathConnectedSpace_and_subsingleton_fundamentalGroup :
    SimplyConnectedSpace X ↔
      PathConnectedSpace X ∧ ∀ x : X, Subsingleton (FundamentalGroup X x) := by
  constructor
  · intro hX
    let _ : SimplyConnectedSpace X := hX
    exact ⟨inferInstance, fun x ↦ inferInstance⟩
  · rintro ⟨hPath, hπ₁⟩
    let _ : PathConnectedSpace X := hPath
    rw [simply_connected_iff_loops_nullhomotopic]
    refine ⟨hPath, fun x γ ↦ ?_⟩
    have hsub : Subsingleton (Path.Homotopic.Quotient x x) := by
      simpa using hπ₁ x
    have hγ : (⟦γ⟧ : Path.Homotopic.Quotient x x) = ⟦Path.refl x⟧ :=
      @Subsingleton.elim (Path.Homotopic.Quotient x x) hsub _ _
    simpa using Quotient.exact hγ
