import Mathlib.LinearAlgebra.AffineSpace.Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Affine Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Text 1.3 characterizes parallel affine subspaces by translation.
- `core/canonical`: the owner is `AffineSubspace.Parallel` (`s ∥ t`), with canonical intrinsic
  criterion `AffineSubspace.parallel_iff_direction_eq_and_eq_bot_iff_eq_bot`.
- `bridge/view`: the translation surface is the pointwise notation `v +ᵥ s`.
- Primitive data vs derived API: direction equality plus `⊥`-equivalence is canonical owner-level
  API; nonempty formulations are thin bridges obtained via `nonempty_iff_ne_bot`.
-/
/- Canonicalization decision record (this pass):
- Codomain/ambient check: this item has no ordered extended codomain; keep the affine-subspace
  owner layer.
- Scalar/ambient structure check: reused owner APIs live at the generic `Ring` affine-space layer;
  no concrete `ℝ`/Euclidean specialization is exposed.
- Owner check: keep `AffineSubspace.Parallel` as the primitive owner and expose translation through
  pointwise `+ᵥ` notation rather than map internals; do not introduce a new local nonemptiness
  owner when canonical set-level nonemptiness already exists.
- Topology check: this item is not topology-facing, so no ambient/intrinsic topology refactor.
- Owner-name check: keep short owner-side theorem names under `AffineSubspace`.
- Notation check: use the textbook-primary pointwise translation notation `v +ᵥ s` on theorem
  surfaces.
-/
namespace AffineSubspace

section

variable {k : Type*} {V : Type*} {P : Type*}
variable [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- A parallel affine subspace is a pointwise translation of the original affine subspace. -/
theorem Parallel.exists_vadd_eq {s t : AffineSubspace k P} (h : s ∥ t) :
    ∃ v : V, v +ᵥ s = t := by
  simpa [eq_comm, AffineSubspace.Parallel, pointwise_vadd_eq_map] using h

/-- Text 1.3: two affine subspaces are parallel exactly when one is a translation of the other. -/
theorem parallel_iff_exists_vadd_eq (s t : AffineSubspace k P) :
    s ∥ t ↔ ∃ v : V, v +ᵥ s = t := by
  simpa [eq_comm] using
    (show s ∥ t ↔ ∃ v : V, t = v +ᵥ s by
      simp [AffineSubspace.Parallel, pointwise_vadd_eq_map])

/-- Symmetric orientation of the translation form of parallel affine subspaces. -/
theorem parallel_iff_exists_eq_vadd (s t : AffineSubspace k P) :
    s ∥ t ↔ ∃ v : V, t = v +ᵥ s := by
  simpa [eq_comm] using parallel_iff_exists_vadd_eq (s := s) (t := t)

/-- The translation of an affine subspace is parallel to the original affine subspace. -/
theorem parallel_vadd (v : V) (s : AffineSubspace k P) :
    s ∥ (v +ᵥ s) :=
  (parallel_iff_exists_vadd_eq (s := s) (t := v +ᵥ s)).2 ⟨v, rfl⟩

/-- Direction equality and `⊥`-equivalence are the intrinsic owner-level criterion
for parallelism. -/
theorem parallel_iff_direction_eq_and_eq_bot (s t : AffineSubspace k P) :
    s ∥ t ↔ s.direction = t.direction ∧ (s = ⊥ ↔ t = ⊥) := by
  simpa using (parallel_iff_direction_eq_and_eq_bot_iff_eq_bot (s₁ := s) (s₂ := t))

/-- Direction equality and intrinsic affine-subspace nonemptiness are a criterion for
parallelism. -/
theorem parallel_iff_direction_eq_and_nonempty (s t : AffineSubspace k P) :
    s ∥ t ↔ s.direction = t.direction ∧ ((s : Set P).Nonempty ↔ (t : Set P).Nonempty) := by
  simpa [AffineSubspace.nonempty_iff_ne_bot, not_iff_not] using
    parallel_iff_direction_eq_and_eq_bot (s := s) (t := t)

end

end AffineSubspace
