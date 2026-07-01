import stacks_project.Chap14.Lemma_14_18_4
import stacks_project.Chap14.Lemma_14_21_5

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

/- Domain-style sampling for Lemma 14.21.4:
- primary domain: simplicial-set skeletons, truncated skeleton adjunctions, and simplicial-set
  dimension bounds;
- sampled owner declarations:
  `SSet.skeleton`,
  `SSet.HasDimensionLT`,
  `SSet.HasDimensionLE`,
  `SSet.hasDimensionLT_iff_of_iso`,
  `truncatedSkeletonIsoSkeleton`;
- best owner abstraction: the canonical owner layer is the dimension predicate
  `SSet.HasDimensionLE`; the chapter bridge identifying `i_{m!} U` with the owner object
  `U.skeleton (m + 1)` is `truncatedSkeletonIsoSkeleton`;
- primitive data: only the truncated simplicial set `U`;
- derived API: the transported instance
  `((SSet.Truncated.sk m).obj U).HasDimensionLE m`, and the pointwise degree-`> m` degeneracy
  statement as a thin corollary.

Source/core/bridge triage:
- `source-facing`: the textbook claim that every simplex of `i_{m!} U` in degree `> m` is
  degenerate;
- `core/canonical`: the dimension bound `((SSet.Truncated.sk m).obj U).HasDimensionLE m`;
- `bridge/view`: the canonical identification of `i_{m!} U` with the simplicial
  `(m + 1)`-skeleton, used only to transport the owner-level instance. -/

-- Proof sketch: first identify `V := (SSet.Truncated.sk m).obj U` with `(SSet.sk m).obj V` by
-- applying `SSet.Truncated.sk m` to the canonical unit isomorphism
-- `U ≅ (SSet.truncation m).obj V`. Then compose with `truncatedSkeletonIsoSkeleton m V` to obtain
-- `V ≅ V.skeleton (m + 1)`, and transport the canonical owner instance
-- `((V.skeleton (m + 1) : SSet)).HasDimensionLT (m + 1)` across that isomorphism.
/-- The simplicial set `i_{m!} U = (SSet.Truncated.sk m).obj U` has dimension at most `m`. -/
instance (m : ℕ) (U : SSet.Truncated m) :
    ((SSet.Truncated.sk m).obj U).HasDimensionLE m := by
  let V : SSet := (SSet.Truncated.sk m).obj U
  let e : V ≅ (V.skeleton (m + 1) : SSet) :=
    (by
      simpa [V] using (SSet.Truncated.sk m).mapIso (asIso ((SSet.skAdj m).unit.app U))) ≪≫
      truncatedSkeletonIsoSkeleton m V
  change V.HasDimensionLT (m + 1)
  rw [SSet.hasDimensionLT_iff_of_iso e (m + 1)]
  infer_instance

/-- Lemma 14.21.4: if `U` is an `m`-truncated simplicial set and `n > m`, then every `n`-simplex
of `i_{m!} U`, i.e. of `(SSet.Truncated.sk m).obj U`, is degenerate. -/
theorem truncatedSkeleton_mem_degenerate_of_lt
    (m : ℕ) (U : SSet.Truncated m) {n : ℕ} (h : m < n)
    (x : ((SSet.Truncated.sk m).obj U) _⦋n⦌) :
    x ∈ ((SSet.Truncated.sk m).obj U).degenerate n := by
  rw [((SSet.Truncated.sk m).obj U).degenerate_eq_top_of_hasDimensionLT (m + 1) n
    (Nat.succ_le_of_lt h)]
  exact Set.mem_univ x
