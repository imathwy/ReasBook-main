import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

open scoped Affine Pointwise
open AffineSubspace Submodule

/-
Source/core/bridge triage:
- `source-facing`: Theorem 1.2 states that a nonempty affine set is parallel to a unique linear
  subspace, identified by its pairwise differences.
- `core/canonical`: the owner abstraction is `AffineSubspace.direction`; the canonical API layer
  should be intrinsic in the affine point space `P`, not specialized to the model case `P = V`.
- `bridge/view`: `AffineSubspace.coe_direction_eq_vsub_set`,
  `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`, and
  `Submodule.toAffineSubspace_direction` supply the canonical comparison with the textbook
  difference-set description.
- Primitive data vs derived API: `direction` is the primitive linear datum; uniqueness from the
  `vsub` carrier is the canonical theorem, while the parallel form first appears intrinsically via
  `mk'` and then as a model-space bridge through `toAffineSubspace`.
- Domain-style sampling: the relevant owner-side declarations in this domain are
  `AffineSubspace.direction`, `AffineSubspace.coe_direction_eq_vsub_set`,
  `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`, and
  `Submodule.toAffineSubspace_direction`.
- Layer target: intrinsic owner first (`direction` + `vsub` carrier equality), then model-space
  bridge (`parallel` with `toAffineSubspace`) as a specialization.
-/
/- Canonicalization decision record (this pass):
- Codomain/ambient check: no ordered extended codomain is exposed; keep the affine-subspace owner
  layer.
- Scalar/ambient structure check: reused APIs already live at the generic `Ring` module layer; no
  `ℝ`/Euclidean specialization is needed.
- Owner check: expose point-witness owner-first uniqueness (`p : M`) as the primary intrinsic API,
  then keep nonempty/pairwise-difference (`-ᵥ`) forms as source-facing bridge statements.
- Topology check: this item is not topology-facing, so no ambient/relative topology refactor.
- Owner-name check: keep short owner-side names and reserve longer `..._eq_vsub` suffixes for
  bridge theorems.
- Notation check: use the textbook-primary surfaces `M ∥ ...`, `mk'`, and `-ᵥ` directly.
-/
recall AffineSubspace.coe_direction_eq_vsub_set
recall AffineSubspace.coe_direction_eq_vsub_set_right
recall AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot
recall AffineSubspace.direction_mk'
recall AffineSubspace.mk'_eq
recall AffineSubspace.Parallel.refl
recall Submodule.toAffineSubspace_direction

namespace AffineSubspace

section Intrinsic

variable {P : Type*} [AddTorsor V P]

/-- Primitive-point owner form of Theorem 1.2: fixing a point `p ∈ M`, the one-sided difference
set `(· -ᵥ p) '' M` determines a unique submodule (namely `M.direction`). -/
theorem existsUnique_direction_eq_vsub_right
    (M : AffineSubspace k P) (p : M) :
    ∃! L : Submodule k V, (↑L : Set V) = ((· -ᵥ (p : P)) '' (↑M : Set P)) := by
  refine ⟨M.direction, ?_, ?_⟩
  · simpa using (coe_direction_eq_vsub_set_right (s := M) p.2)
  · intro L hL
    apply SetLike.coe_injective
    rw [hL, coe_direction_eq_vsub_set_right (s := M) p.2]

/-- Source-facing pairwise-difference form of Theorem 1.2: for a nonempty affine subspace, the set
of pairwise differences determines a unique submodule (namely `M.direction`). -/
theorem existsUnique_direction_eq_vsub
    (M : AffineSubspace k P) (hM : Nonempty M) :
    ∃! L : Submodule k V, (↑L : Set V) = ((↑M : Set P) -ᵥ (↑M : Set P) : Set V) := by
  have hM_set : (↑M : Set P).Nonempty := Set.nonempty_coe_sort.mp hM
  refine ⟨M.direction, coe_direction_eq_vsub_set hM_set, ?_⟩
  intro L hL
  apply SetLike.coe_injective
  rw [hL, coe_direction_eq_vsub_set hM_set]

/-- Primitive-point owner form of Theorem 1.2: fixing `p ∈ M`, there is a unique direction `L`
such that `M` is parallel to the affine translate `mk' p L`. -/
theorem existsUnique_parallel_mk'_of_mem
    (M : AffineSubspace k P) (p : M) :
    ∃! L : Submodule k V, M ∥ mk' p L := by
  refine ⟨M.direction, ?_, ?_⟩
  · simpa [mk'_eq p.2] using (AffineSubspace.Parallel.refl M)
  · intro L hL
    have hdir : M.direction = (mk' (p : P) L).direction := hL.direction_eq
    have hdir' : M.direction = L := by simpa using hdir
    exact hdir'.symm

/-- Intrinsic bridge form of Theorem 1.2: a nonempty affine subspace is parallel to the unique
translate owner `mk' p L`, uniformly for all points `p ∈ M`. -/
theorem existsUnique_parallel_mk'
    (M : AffineSubspace k P) (hM : Nonempty M) :
    ∃! L : Submodule k V, ∀ p : M, M ∥ mk' p L := by
  refine ⟨M.direction, ?_, ?_⟩
  · intro p
    simpa [mk'_eq p.2] using (AffineSubspace.Parallel.refl M)
  · intro L hL
    rcases hM with ⟨p⟩
    have hdir : M.direction = (mk' (p : P) L).direction := (hL p).direction_eq
    have hdir' : M.direction = L := by simpa using hdir
    exact hdir'.symm

/-- Intrinsic parallel form of Theorem 1.2: for each point `p` in a nonempty affine subspace,
`M` is parallel to the affine translate `mk' p L` of the unique difference submodule `L`. -/
theorem existsUnique_parallel_mk'_eq_vsub
    (M : AffineSubspace k P) (hM : Nonempty M) :
    ∃! L : Submodule k V,
      (↑L : Set V) = ((↑M : Set P) -ᵥ (↑M : Set P) : Set V) ∧
      ∀ p : M, M ∥ mk' p L := by
  have hM_set : (↑M : Set P).Nonempty := Set.nonempty_coe_sort.mp hM
  refine ⟨M.direction, ?_, ?_⟩
  · refine ⟨coe_direction_eq_vsub_set hM_set, ?_⟩
    intro p
    simpa [mk'_eq p.2] using (AffineSubspace.Parallel.refl M)
  · intro L hL
    apply SetLike.coe_injective
    rw [hL.1, coe_direction_eq_vsub_set hM_set]

end Intrinsic

/-- Model-space owner bridge: every nonbottom affine subspace is parallel to the affine subspace
through the origin induced by its direction. -/
theorem parallel_toAffineSubspace_direction
    (M : AffineSubspace k V) (hM : M ≠ ⊥) :
    M ∥ M.direction.toAffineSubspace := by
  have hdirection_ne_bot : (M.direction.toAffineSubspace : AffineSubspace k V) ≠ ⊥ :=
    (nonempty_iff_ne_bot _).1 ⟨0, by simp⟩
  refine (parallel_iff_direction_eq_and_eq_bot_iff_eq_bot).2 ?_
  refine ⟨(toAffineSubspace_direction M.direction).symm, ?_⟩
  constructor
  · exact fun h => (hM h).elim
  · exact fun h => (hdirection_ne_bot h).elim

/-- Owner-first model-space form of Theorem 1.2: in `V`, each nonbottom affine set is parallel to
one unique submodule through the origin. -/
theorem existsUnique_parallel_toAffineSubspace
    (M : AffineSubspace k V) (hM : M ≠ ⊥) :
    ∃! L : Submodule k V, M ∥ L.toAffineSubspace := by
  refine ⟨M.direction, ?_, ?_⟩
  · exact parallel_toAffineSubspace_direction M hM
  · intro L hL
    have hdir : M.direction = (L.toAffineSubspace : AffineSubspace k V).direction := hL.direction_eq
    have hdir' : M.direction = L := by simpa [toAffineSubspace_direction] using hdir
    exact hdir'.symm

/-- Theorem 1.2, source-facing model-space bridge: in `V`, each nonempty affine set is parallel
to a unique submodule whose carrier is the pairwise-difference set `M - M`. -/
theorem existsUnique_parallel_toAffineSubspace_eq_vsub
    (M : AffineSubspace k V) (hM : Nonempty M) :
    ∃! L : Submodule k V,
      (↑L : Set V) = ((↑M : Set V) -ᵥ (↑M : Set V) : Set V) ∧ M ∥ L.toAffineSubspace := by
  have hM_set : (↑M : Set V).Nonempty := Set.nonempty_coe_sort.mp hM
  have hM_ne_bot : M ≠ ⊥ := (nonempty_iff_ne_bot M).1 hM_set
  refine ⟨M.direction, ?_, ?_⟩
  · refine ⟨coe_direction_eq_vsub_set hM_set, ?_⟩
    exact parallel_toAffineSubspace_direction M hM_ne_bot
  intro L hL
  apply SetLike.coe_injective
  rw [hL.1, coe_direction_eq_vsub_set hM_set]

end AffineSubspace
