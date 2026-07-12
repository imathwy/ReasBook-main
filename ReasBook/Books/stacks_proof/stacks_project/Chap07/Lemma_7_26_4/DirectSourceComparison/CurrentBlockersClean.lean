/-
Status snapshot for
`stacks_project/Chap07/Lemma_7_26_4/DirectSourceComparison.lean`.

Last checked on 2026-06-23 with:

  lake env lean -T20000 \
    stacks_project/Chap07/Lemma_7_26_4/DirectSourceComparison.lean

Current status:

* `DirectSourceComparison.lean` compiles.
* The old q-normalized presheaf descent blocker has been resolved by
  `localized_cover_descent_q_component_presheaf_hom_descent`.
* The old final sheafified descent square blocker has been resolved by
  `localized_cover_descent_glued_descent_iso_comm`.
* This file is intentionally documentation-only, imports nothing, and should
  elaborate cleanly by itself.

Proof discipline for future edits in this directory:

* Prefer named object equalities, section equalities, and HEq bridges.
* Shape transport-heavy goals with `change`, `rw`, and `calc`.
* Use small `simp only` or tightly scoped `simpa` after the target has already
  been made explicit.
* Avoid broad `simp`/`simpa` calls whose success depends on unfolding a large
  pseudofunctor or sheafification normal form.
-/
