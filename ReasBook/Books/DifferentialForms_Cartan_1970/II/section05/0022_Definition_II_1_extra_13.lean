import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition II.1-extra-13: the textbook notion of a simply connected open set is the canonical
predicate `IsSimplyConnected` on subsets. -/
recall IsSimplyConnected

/-- An open subset of `ℂ` is simply connected exactly when it is connected and every loop in it is
homotopic within the set to a constant loop. -/
-- Proof sketch: combine `isSimplyConnected_iff_exists_homotopy_refl_forall_mem` with
-- `IsOpen.isConnected_iff_isPathConnected` for open subsets of `ℂ`.
theorem isSimplyConnected_iff_isConnected_and_loops_homotopic_to_point {D : Set ℂ} (hD : IsOpen D) :
    IsSimplyConnected D ↔
      IsConnected D ∧ ∀ x, ∀ γ : Path x x, (∀ t, γ t ∈ D) →
        ∃ F : γ.Homotopy (Path.refl x), ∀ t, F t ∈ D := by
  -- Replace the textbook connectedness clause by the path-connected clause used in mathlib.
  have hconn : IsPathConnected D ↔ IsConnected D := by
    simpa using (hD.isConnected_iff_isPathConnected).symm
  -- Then rewrite simple connectedness by null-homotopy of loops and substitute the first conjunct.
  rw [isSimplyConnected_iff_exists_homotopy_refl_forall_mem]
  simp [hconn]
