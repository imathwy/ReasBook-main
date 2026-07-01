import Mathlib.LinearAlgebra.AffineSpace.Pointwise
import Mathlib.Tactic.Recall

open scoped Affine Pointwise

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 1.2.1 says that translating an affine subset yields another affine subset;
  specializing to `P = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement.
- `core/canonical`: the owner abstraction is the pointwise translation action on
  `AffineSubspace k P`, implemented by `AffineSubspace.pointwiseVAdd`.
- `bridge/view`: `AffineSubspace.pointwise_vadd_eq_map` identifies the translation action with the
  canonical affine-equivalence map; `AffineSubspace.vadd_mem_pointwise_vadd_iff` gives the
  intrinsic membership bridge for the translated affine subspace; and
  `AffineSubspace.coe_pointwise_vadd` together with set-level owners `Set.mem_vadd_set` /
  `Set.image_vadd` read the resulting affine subspace back as the textbook translated set.
- Domain-style sampling used here:
  `Set.vaddSet` for the ambient set translation action,
  `AffineSubspace.pointwiseVAdd` for translation of affine subspaces,
  `AffineSubspace.pointwise_vadd_eq_map` for the affine-equivalence description, and
  `AffineSubspace.vadd_mem_pointwise_vadd_iff` / `AffineSubspace.coe_pointwise_vadd` with
  `Set.mem_vadd_set` / `Set.image_vadd` for intrinsic- and set-level bridge views.
- Primitive data vs derived API: the pointwise `VAdd` action on affine subspaces is the primitive
  owner data; the map description and the carrier equality are derived bridge API.
- Layer target: `core/canonical` for the affine-subspace translation owner, then `bridge/view` for
  the textbook set translation.
- Canonicalization decision record (this pass):
  - Codomain/ambient check: no codomain is present; keep the ambient layer at generic
    affine-space data `[Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]`.
  - Scalar check: no concrete scalar is needed; keep fully generic `k`.
  - Owner check: keep intrinsic membership over `v +ᵥ s` as the primary theorem surface; reuse
    canonical set-level bridges directly instead of restating them as local wrappers.
  - Topology check: this item is not topology-facing.
  - Notation check: use `+ᵥ` directly on source-facing theorem surfaces.
-/
namespace AffineSubspace

/- Text 1.2.1: translating an affine set is the canonical pointwise `VAdd` action on affine
subspaces. -/
recall AffineSubspace.pointwiseVAdd

/- The canonical bridge views of that translation are `pointwise_vadd_eq_map`
(affine-equivalence view), `vadd_mem_pointwise_vadd_iff` (intrinsic membership view), and
`coe_pointwise_vadd` (set-level coercion view). -/
recall pointwise_vadd_eq_map
recall vadd_mem_pointwise_vadd_iff
recall coe_pointwise_vadd
recall Set.mem_vadd_set
recall Set.image_vadd

section

variable {k V P : Type*}
  [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- Intrinsic membership form of translated affine subspaces: membership in `v +ᵥ s` is equivalent
to membership in `s` after translating back by `-v`. -/
theorem mem_vadd_iff_neg_vadd_mem (v : V) (s : AffineSubspace k P) (x : P) :
    x ∈ v +ᵥ s ↔ (-v) +ᵥ x ∈ s := by
  simpa [vadd_vadd] using
    (vadd_mem_pointwise_vadd_iff (v := v) (s := s) (p := (-v) +ᵥ x))

/-- Symmetric intrinsic membership form of translated affine subspaces. -/
theorem neg_vadd_mem_iff_mem_vadd (v : V) (s : AffineSubspace k P) (x : P) :
    (-v) +ᵥ x ∈ s ↔ x ∈ v +ᵥ s := by
  exact (mem_vadd_iff_neg_vadd_mem (v := v) (s := s) (x := x)).symm

end

end AffineSubspace
