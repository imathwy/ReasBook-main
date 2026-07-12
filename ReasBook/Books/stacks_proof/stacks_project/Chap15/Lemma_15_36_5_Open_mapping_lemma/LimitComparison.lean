import Mathlib

noncomputable section

universe u v

open scoped Topology Pointwise

variable {N : Type u} {M : Type v}
variable [TopologicalSpace N] [AddCommGroup N] [IsTopologicalAddGroup N]
variable [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [T2Space M]

/-- Helper for Lemma 15.36.5 (Open mapping lemma): if a source sequence converges to `z` and the
target-side remainder tends to `0`, then the corrected image sequence converges to `u z`. -/
lemma tendsto_map_partial_sum_add_remainder
    (u : N →ₜ+ M) {s : ℕ → N} {r : ℕ → M} {z : N}
    (hs : Filter.Tendsto s Filter.atTop (𝓝 z))
    (hr : Filter.Tendsto r Filter.atTop (𝓝 (0 : M))) :
    Filter.Tendsto (fun m ↦ u (s m) + r m) Filter.atTop (𝓝 (u z)) := by
  -- First transport the source-side limit through `u`.
  have hu : Filter.Tendsto (fun m ↦ u (s m)) Filter.atTop (𝓝 (u z)) := by
    exact (u.continuous.tendsto z).comp hs
  -- Then add the remainder term, which vanishes in the target.
  simpa using hu.add hr

/-- Helper for Lemma 15.36.5 (Open mapping lemma): if every stage of the corrected image sequence
is equal to a fixed target point `y`, then separatedness identifies `y` with the image of the
source-side limit. -/
lemma eq_map_limit_of_partial_sum_add_remainder
    (u : N →ₜ+ M) {s : ℕ → N} {r : ℕ → M} {y : M} {z : N}
    (hy : ∀ m, y = u (s m) + r m)
    (hs : Filter.Tendsto s Filter.atTop (𝓝 z))
    (hr : Filter.Tendsto r Filter.atTop (𝓝 (0 : M))) :
    y = u z := by
  -- Route correction: isolate the Hausdorff limit comparison from the recursive construction.
  have hsum :
      Filter.Tendsto (fun m ↦ u (s m) + r m) Filter.atTop (𝓝 (u z)) :=
    tendsto_map_partial_sum_add_remainder u hs hr
  have hconst : Filter.Tendsto (fun _ : ℕ => y) Filter.atTop (𝓝 y) :=
    tendsto_const_nhds
  have hsum' : Filter.Tendsto (fun _ : ℕ => y) Filter.atTop (𝓝 (u z)) := by
    -- Rewrite the corrected sequence to the constant sequence `y`.
    simpa [funext fun m ↦ (hy m).symm] using hsum
  -- Uniqueness of limits in the separated target gives the desired equality.
  exact tendsto_nhds_unique hconst hsum'
