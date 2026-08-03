module

public import Mathlib.Topology.Constructions

@[expose] public section

universe u

namespace Fin

/-- The canonical homeomorphism that appends a final coordinate to a finite dependent
product. -/
def snocHomeomorph {n : ℕ} (X : Fin (n + 1) → Type u)
    [(i : Fin (n + 1)) → TopologicalSpace (X i)] :
    ((i : Fin n) → X i.castSucc) × X (Fin.last n) ≃ₜ ((i : Fin (n + 1)) → X i) where
  __ := (Equiv.prodComm _ _).trans (Fin.snocEquiv X)
  continuous_toFun := by
    rw [show ((Equiv.prodComm _ _).trans (snocEquiv X)).toFun =
      fun p : ((i : Fin n) → X i.castSucc) × X (Fin.last n) ↦ snoc p.1 p.2 by rfl]
    apply continuous_pi
    intro i
    refine lastCases ?_ ?_ i
    · simpa only [snoc_last] using
        (continuous_snd :
          Continuous fun p : ((i : Fin n) → X i.castSucc) × X (Fin.last n) ↦ p.2)
    · intro j
      simpa only [snoc_castSucc] using
        (continuous_apply j).comp'
          (continuous_fst :
            Continuous fun p : ((i : Fin n) → X i.castSucc) × X (Fin.last n) ↦ p.1)
  continuous_invFun := by
    rw [show ((Equiv.prodComm _ _).trans (snocEquiv X)).invFun =
      fun q : (i : Fin (n + 1)) → X i ↦ (init q, q (Fin.last n)) by rfl]
    apply Continuous.prodMk
    · apply continuous_pi
      intro j
      exact continuous_apply j.castSucc
    · exact continuous_apply (Fin.last n)

/-- The underlying equivalence of `Fin.snocHomeomorph` is the standard tuple snoc
equivalence, with its two input factors exchanged. -/
@[simp]
theorem snocHomeomorph_toEquiv {n : ℕ} (X : Fin (n + 1) → Type u)
    [(i : Fin (n + 1)) → TopologicalSpace (X i)] :
    (snocHomeomorph X).toEquiv = (Equiv.prodComm _ _).trans (snocEquiv X) := rfl

/-- Applying `Fin.snocHomeomorph` appends the specified final coordinate. -/
@[simp]
theorem snocHomeomorph_apply {n : ℕ} (X : Fin (n + 1) → Type u)
    [(i : Fin (n + 1)) → TopologicalSpace (X i)]
    (p : (i : Fin n) → X i.castSucc) (x : X (Fin.last n)) :
    snocHomeomorph X (p, x) = snoc p x := rfl

/-- The inverse of `Fin.snocHomeomorph` recovers the initial coordinates and the final
coordinate. -/
@[simp]
theorem snocHomeomorph_symm_apply {n : ℕ} (X : Fin (n + 1) → Type u)
    [(i : Fin (n + 1)) → TopologicalSpace (X i)] (q : (i : Fin (n + 1)) → X i) :
    (snocHomeomorph X).symm q = (init q, q (Fin.last n)) := rfl

end Fin
