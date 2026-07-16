import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

variable {k V : Type*} [Ring k] [AddCommGroup V] [Module k V]

open AffineSubspace Submodule

/-
Source/core/bridge triage:
- `source-facing`: Theorem 1.1 says an affine set in a vector space is a linear subspace
  exactly when it contains the origin.
- `core/canonical`: the owner abstraction is `AffineSubspace k V`, with the canonical comparison
  datum `AffineSubspace.direction`, the intrinsic constructor `AffineSubspace.mk'`, and the
  canonical linear-to-affine coercion `Submodule.toAffineSubspace`.
- `bridge/view`: the primary bridge below is the intrinsic point-membership criterion
  `AffineSubspace.mk' p s.direction = s ↔ p ∈ s`; the origin criterion is then the thin
  specialization `p = 0` in the model affine space `P = V`.
- Domain-style sampling: the relevant owner-side declarations are `AffineSubspace.direction`,
  `AffineSubspace.mk'`, `AffineSubspace.mk'_eq`, `Submodule.toAffineSubspace`, and
  `Submodule.mem_toAffineSubspace`.
- Primitive data vs derived API: `direction` and `mk'` are owner-level primitives; both the
  point-membership and origin criteria are derived bridge theorems.
- Layer target: `bridge/view`; there is no separate source-defined owner here beyond the canonical
  affine-subspace object and its direction.
-/
/- Canonicalization decision record (this pass):
- Codomain/ambient check: no ordered extended codomain appears; this item is purely affine/module.
- Scalar/ambient structure check:
  `AffineSubspace`/`Submodule.toAffineSubspace` APIs here are already native to the
  generic `Ring`-module layer; no `ℝ`-specific assumptions are present.
- Owner check: keep `AffineSubspace` and `Submodule` as the canonical owners; expose the intrinsic
  owner bridge `mk' p s.direction = s ↔ p ∈ s`, with the origin criterion as a thin derived
  specialization and the `toAffineSubspace` rewrite kept as a public owner bridge.
- Topology check: this item is not topology-facing, so no ambient-vs-relative topology refactor.
- Owner-name/notation check: keep short owner names and existing canonical notation (`mk'`,
  `toAffineSubspace`) on theorem surfaces.
-/
recall mk'_eq
recall mem_mk'
recall self_mem_mk'
recall mem_toAffineSubspace

namespace AffineSubspace

variable {P : Type*} [AddTorsor V P]

/-- Helper for Theorem 1.1: an affine subspace is the affine translate built from a point and its
direction iff that point belongs to the subspace. -/
@[simp] theorem mk'_direction_eq_iff_mem (s : AffineSubspace k P) (p : P) :
    mk' p s.direction = s ↔ p ∈ s := by
  constructor
  · intro hs
    -- Rewriting along the assumed equality reduces membership to the canonical base-point fact.
    rw [← hs]
    exact self_mem_mk' p s.direction
  · intro hp
    -- Once the point lies in the affine subspace, `mk'_eq` identifies the rebuilt translate.
    simpa using (mk'_eq (s := s) hp)

end AffineSubspace

namespace Submodule

/-- Helper for Theorem 1.1: the intrinsic `mk'` presentation at the origin agrees with the
model-space owner `toAffineSubspace`. -/
@[simp] theorem mk'_zero_eq_toAffineSubspace (S : Submodule k V) :
    AffineSubspace.mk' (0 : V) S = S.toAffineSubspace := by
  -- Both affine subspaces have the same carrier, so extensionality reduces the claim to membership.
  ext x
  simp [Submodule.mem_toAffineSubspace]

end Submodule

namespace AffineSubspace

/-- Theorem 1.1, canonical owner form: an affine set in a module coincides with the affine
subspace through the origin induced by its direction iff it contains the origin. -/
@[simp] theorem direction_toAffineSubspace_eq_iff_zero_mem
    (s : AffineSubspace k V) :
    s.direction.toAffineSubspace = s ↔ 0 ∈ s := by
  -- Specialize the point-membership bridge to the origin and rewrite `mk' 0` as `toAffineSubspace`.
  simpa [Submodule.mk'_zero_eq_toAffineSubspace] using
    (mk'_direction_eq_iff_mem (s := s) (p := (0 : V)))

/-- Theorem 1.1, source-facing existence form: an affine set is a linear subspace exactly when it
contains the origin. -/
theorem exists_toAffineSubspace_eq_iff_zero_mem
    (s : AffineSubspace k V) :
    (∃ S : Submodule k V, S.toAffineSubspace = s) ↔ 0 ∈ s := by
  constructor
  · rintro ⟨S, rfl⟩
    -- Any linear submodule contains the origin, so its affine avatar does as well.
    simp
  · intro h0
    -- The direction submodule is the canonical witness once the affine subspace contains `0`.
    exact ⟨s.direction, (direction_toAffineSubspace_eq_iff_zero_mem (s := s)).2 h0⟩

end AffineSubspace
