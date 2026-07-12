import Mathlib.Order.Filter.Extr
import Mathlib.Order.SaddlePoint

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.7 introduces the notion of a saddle point of the Lagrangian
  `L u⋆ x`, with maximization in the dual variable `u⋆` and minimization in the primal variable
  `x`.
- `core/canonical`: mathlib already owns the ambient notion as `_root_.IsSaddlePointOn X Y f a b`.
- `bridge/view`: the source writes kernels as `K u v` with maximization in `u` and minimization in
  `v`, so this file exposes a source-ordered owner
  `Bifunction.IsSaddlePointOn C D K u v := _root_.IsSaddlePointOn D C (Function.swap K) v u`.
- owner policy: expose the source-facing bridge API and avoid a second public layer that merely
  repeats swapped raw-owner statements.

Domain-style sampling used here:
- `_root_.IsSaddlePointOn` from `Mathlib.Order.SaddlePoint`;
- `isMinOn_iff` from `Mathlib.Order.Filter.Extr`;
- `isMaxOn_iff` from `Mathlib.Order.Filter.Extr`;

Primitive data vs derived API:
- primitive owner data: the domain sets `C`, `D`, the bifunction `K`, and the candidate pair
  `(u, v)`;
- source-facing owner: `Bifunction.IsSaddlePointOn C D K u v`;
- canonical bridge owner: `_root_.IsSaddlePointOn D C (Function.swap K) v u`;
- primitive bridge API: the full source-order two-variable inequality
  `∀ u' ∈ C, ∀ v' ∈ D, K u' v ≤ K u v'`;
- derived API: source-order one-sided inequalities and `IsMaxOn`/`IsMinOn` reformulations.
-/

universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w} [Preorder β]

namespace Bifunction

/-- Definition 6.28.7, source-ordered owner: `u` is maximized on `C`, `v` is minimized on `D`,
for a kernel written as `K u v`. -/
def IsSaddlePointOn (C : Set E) (D : Set F) (K : E → F → β) (u : E) (v : F) : Prop :=
  _root_.IsSaddlePointOn D C (Function.swap K) v u

/-- Whole-space specialization of `Bifunction.IsSaddlePointOn`. -/
abbrev IsSaddlePoint (K : E → F → β) (u : E) (v : F) : Prop :=
  IsSaddlePointOn Set.univ Set.univ K u v

/-- Primitive source-order inequality characterization:
`(u, v)` is a source-ordered saddle point on `C × D` iff every rectangle-corner inequality
`K u' v ≤ K u v'` holds for `u' ∈ C`, `v' ∈ D`. -/
theorem isSaddlePointOn_iff_forall
    {C : Set E} {D : Set F} {K : E → F → β} {u : E} {v : F} :
    IsSaddlePointOn C D K u v ↔
      ∀ u' ∈ C, ∀ v' ∈ D, K u' v ≤ K u v' := by
  constructor
  · intro h u' hu' v' hv'
    exact h v' hv' u' hu'
  · intro h v' hv' u' hu'
    exact h u' hu' v' hv'

/-- Primitive whole-space source-order inequality characterization of Definition 6.28.7. -/
theorem isSaddlePoint_iff_forall
    {K : E → F → β} {u : E} {v : F} :
    IsSaddlePoint K u v ↔
      ∀ u' : E, ∀ v' : F, K u' v ≤ K u v' := by
  simpa [IsSaddlePoint] using
    (isSaddlePointOn_iff_forall
      (C := (Set.univ : Set E)) (D := (Set.univ : Set F))
      (K := K) (u := u) (v := v))

-- Proof sketch: expand the swapped canonical owner at `x = v` and `y = u`, obtaining the two
-- source-order one-sided inequalities; conversely compose those inequalities by transitivity.
/-- One-sided source-order inequality characterization of `Bifunction.IsSaddlePointOn` on `C × D`,
derived from `isSaddlePointOn_iff_forall` under membership of the distinguished pair. -/
theorem isSaddlePointOn_iff_source_order
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      (∀ u' ∈ C, K u' v ≤ K u v) ∧
      ∀ v' ∈ D, K u v ≤ K u v' := by
  constructor
  · intro h
    rcases (isSaddlePointOn_iff_forall (C := C) (D := D) (K := K) (u := u) (v := v)).1 h with hrect
    refine ⟨?_, ?_⟩
    · intro u' hu'
      exact hrect u' hu' v hv
    · intro v' hv'
      exact hrect u hu v' hv'
  · intro h v' hv' u' hu'
    exact le_trans (h.1 u' hu') (h.2 v' hv')

/-- Extrema reformulation of `isSaddlePointOn_iff_source_order`. -/
theorem isSaddlePointOn_iff_isMaxOn_isMinOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      IsMaxOn (fun u' : E ↦ K u' v) C u ∧
      IsMinOn (fun v' : F ↦ K u v') D v := by
  simpa [isMaxOn_iff, isMinOn_iff] using
    (isSaddlePointOn_iff_source_order (C := C) (D := D) (K := K) (u := u) (v := v) hu hv)

/-- Extrema reformulation of `isSaddlePointOn_iff_source_order` with `(IsMinOn, IsMaxOn)` order. -/
theorem isSaddlePointOn_iff_isMinOn_isMaxOn
    {C : Set E} {D : Set F} {K : E → F → β}
    {u : E} (hu : u ∈ C) {v : F} (hv : v ∈ D) :
    IsSaddlePointOn C D K u v ↔
      IsMinOn (fun v' : F ↦ K u v') D v ∧
      IsMaxOn (fun u' : E ↦ K u' v) C u := by
  simpa [and_comm] using
    (isSaddlePointOn_iff_isMaxOn_isMinOn (C := C) (D := D) (K := K) (u := u) (v := v) hu hv)

/-- Whole-space source-order inequality characterization of Definition 6.28.7. -/
theorem isSaddlePoint_iff_source_order
    {K : E → F → β} {u : E} {v : F} :
    IsSaddlePoint K u v ↔
      (∀ u' : E, K u' v ≤ K u v) ∧
      ∀ v' : F, K u v ≤ K u v' := by
  constructor
  · intro h
    rcases (isSaddlePoint_iff_forall (K := K) (u := u) (v := v)).1 h with hrect
    refine ⟨?_, ?_⟩
    · intro u'
      exact hrect u' v
    · intro v'
      exact hrect u v'
  · intro h
    exact (isSaddlePoint_iff_forall (K := K) (u := u) (v := v)).2
      (fun u' v' ↦ le_trans (h.1 u') (h.2 v'))

/-- Whole-space extrema reformulation of Definition 6.28.7. -/
theorem isSaddlePoint_iff_isMaxOn_isMinOn
    {K : E → F → β} {u : E} {v : F} :
    IsSaddlePoint K u v ↔
      IsMaxOn (fun u' : E ↦ K u' v) (Set.univ : Set E) u ∧
      IsMinOn (fun v' : F ↦ K u v') (Set.univ : Set F) v := by
  simpa [IsSaddlePoint] using
    (isSaddlePointOn_iff_isMaxOn_isMinOn
      (C := (Set.univ : Set E)) (D := (Set.univ : Set F))
      (K := K) (u := u) (v := v) (by simp) (by simp))

end Bifunction

end
