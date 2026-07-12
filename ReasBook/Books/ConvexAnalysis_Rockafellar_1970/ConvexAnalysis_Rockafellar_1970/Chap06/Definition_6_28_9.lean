import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {E : Type u} {F : Type v} {β : Type w} [Preorder β]

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.9 specializes the saddle-point notion to a Lagrangian
  `L u⋆ x`, with the dual variable `u⋆` maximized over the multiplier set `Eᵣ` and the primal
  variable `x` minimized over the feasible set `C`.
- `core/canonical`: Chapter 6 now uses the source-ordered owner
  `Bifunction.IsSaddlePointOn C D K u v`.
- `bridge/view`: this source owner is definitionally
  `_root_.IsSaddlePointOn D C (Function.swap K) v u`; swapped-kernel views remain available
  from `Chap06.Definition_6_28_7` when needed.

Domain-style sampling used here:
- `Bifunction.IsSaddlePointOn` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_forall` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_source_order` from `Chap06.Definition_6_28_7`;
- `Bifunction.isSaddlePointOn_iff_isMaxOn_isMinOn` from `Chap06.Definition_6_28_7`.

Primitive data vs derived API:
- primitive owner data: the primal domain `C`, the dual domain `Eᵣ`, the Lagrangian `L`, and the
  candidate pair `(u⋆, x)`;
- source-facing owner API: the Chapter 6 owner `Bifunction.IsSaddlePointOn Er C L u⋆ x`;
- derived source-facing API: the Lagrangian specialization obtained by instantiating that bridge at
  `K = L`.

Layer target: a `source-facing` owner surface for Definition 6.28.9.
-/

/-- Definition 6.28.9: a pair `(u⋆, x)` with `x ∈ C` and `u⋆ ∈ Eᵣ` is a saddle point of the
Lagrangian `L` exactly when, on the primal feasible set `C` and the dual multiplier set `Eᵣ`,
the dual variable `u⋆` is a maximizer of `L · x` and the primal variable `x` is a minimizer of
`L u⋆ ·`. -/
theorem lagrangian_mem_iff_isMaxOn_isMinOn
    {C : Set E} {Er : Set F} {L : F → E → β}
    {x : E} {uStar : F} :
    (uStar ∈ Er ∧ x ∈ C ∧ IsSaddlePointOn Er C L uStar x) ↔
      uStar ∈ Er ∧ x ∈ C ∧
        IsMaxOn (L · x) Er uStar ∧
        IsMinOn (L uStar) C x := by
  constructor
  · rintro ⟨huStar, hx, hsaddle⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_isMaxOn_isMinOn
          (C := Er) (D := C) (K := L) huStar hx).1 hsaddle⟩
  · rintro ⟨huStar, hx, hmaxmin⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_isMaxOn_isMinOn
          (C := Er) (D := C) (K := L) huStar hx).2 hmaxmin⟩

/-- Membership-hypothesis formulation of Definition 6.28.9 in extrema-owner form. -/
theorem lagrangian_iff
    {C : Set E} {Er : Set F} {L : F → E → β}
    {uStar : F} (huStar : uStar ∈ Er) {x : E} (hx : x ∈ C) :
    IsSaddlePointOn Er C L uStar x ↔
      IsMaxOn (L · x) Er uStar ∧
      IsMinOn (L uStar) C x := by
  simpa using
    (isSaddlePointOn_iff_isMaxOn_isMinOn
      (C := Er) (D := C) (K := L) huStar hx)

/-- Primitive rectangle-corner inequality form of Definition 6.28.9, with no distinguished-point
membership assumptions. -/
theorem lagrangian_iff_forall_rect
    {C : Set E} {Er : Set F} {L : F → E → β}
    {x : E} {uStar : F} :
    IsSaddlePointOn Er C L uStar x ↔
      ∀ u ∈ Er, ∀ y ∈ C, L u x ≤ L uStar y := by
  simpa using
    (isSaddlePointOn_iff_forall (C := Er) (D := C) (K := L) (u := uStar) (v := x))

/-- One-sided source-order inequality form of Definition 6.28.9 under distinguished-point
membership assumptions. -/
theorem lagrangian_mem_iff_source_order
    {C : Set E} {Er : Set F} {L : F → E → β}
    {x : E} {uStar : F} :
    (uStar ∈ Er ∧ x ∈ C ∧ IsSaddlePointOn Er C L uStar x) ↔
      uStar ∈ Er ∧ x ∈ C ∧
        (∀ u ∈ Er, L u x ≤ L uStar x) ∧
        (∀ y ∈ C, L uStar x ≤ L uStar y) := by
  constructor
  · rintro ⟨huStar, hx, hsaddle⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_source_order
          (C := Er) (D := C) (K := L) huStar hx).1 hsaddle⟩
  · rintro ⟨huStar, hx, horder⟩
    exact
      ⟨huStar, hx,
        (isSaddlePointOn_iff_source_order
          (C := Er) (D := C) (K := L) huStar hx).2 horder⟩

/-- Membership-hypothesis formulation of Definition 6.28.9 in one-sided source-order form. -/
theorem lagrangian_iff_forall
    {C : Set E} {Er : Set F} {L : F → E → β}
    {uStar : F} (huStar : uStar ∈ Er) {x : E} (hx : x ∈ C) :
    IsSaddlePointOn Er C L uStar x ↔
      (∀ u ∈ Er, L u x ≤ L uStar x) ∧
      (∀ y ∈ C, L uStar x ≤ L uStar y) := by
  simpa using
    (isSaddlePointOn_iff_source_order
      (C := Er) (D := C) (K := L) huStar hx)

/-- Universe-domain specialization of `lagrangian_iff`, eliminating proof-only membership
arguments from the theorem surface. -/
theorem lagrangian_univ_iff
    {L : F → E → β} {x : E} {uStar : F} :
    IsSaddlePoint L uStar x ↔
      IsMaxOn (L · x) (Set.univ : Set F) uStar ∧
      IsMinOn (L uStar) (Set.univ : Set E) x := by
  simpa using (isSaddlePoint_iff_isMaxOn_isMinOn (K := L) (u := uStar) (v := x))

/-- Primitive rectangle-corner inequality form of `lagrangian_univ_iff`. -/
theorem lagrangian_univ_iff_forall_rect
    {L : F → E → β} {x : E} {uStar : F} :
    IsSaddlePoint L uStar x ↔
      (∀ u : F, ∀ y : E, L u x ≤ L uStar y) := by
  simpa using (isSaddlePoint_iff_forall (K := L) (u := uStar) (v := x))

/-- Raw pointwise inequality form of `lagrangian_univ_iff`. -/
theorem lagrangian_univ_iff_forall
    {L : F → E → β} {x : E} {uStar : F} :
    IsSaddlePoint L uStar x ↔
      (∀ u : F, L u x ≤ L uStar x) ∧
      (∀ y : E, L uStar x ≤ L uStar y) := by
  simpa using (isSaddlePoint_iff_source_order (K := L) (u := uStar) (v := x))

end Bifunction

end
