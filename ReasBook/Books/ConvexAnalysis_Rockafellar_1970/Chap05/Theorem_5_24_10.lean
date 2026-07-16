import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_5_24_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1

-- Declarations for this item were appended by the statement pipeline.

noncomputable section

open Bornology Function
open scoped Rockafellar SetRel

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.24.10 studies the set `∂f(S) = ⋃ x ∈ S, ∂f(x)` for a nonempty
  closed bounded set `S`, proves nonemptiness/closedness of this set from `S ⊆ riDom(f)`,
  proves boundedness from `S ⊆ interior (dom(f))`, and then uses the supremum of the dual norms
  of its elements to bound directional derivatives and the oscillation of `f` on `S`.
- `core/canonical`: the owner abstraction is the upstream intrinsic graph/image layer from
  Definition 5.24.3, namely `subdifferentialGraph` and `subdifferentialImage`, surfaced here by
  the notation `∂f(S)`, together with the Chapter 23 directional-derivative owner
  `directionalDerivativeAt` and mathlib's canonical `IsBounded`, `IsClosed`, and
  `LipschitzOnWith`.
- `bridge/view`: on inner-product spaces, `Function.subdifferentialGraph f` is only the
  Fréchet-Riesz specialization of the same owner. It is not the main public surface of this file.

Domain-style sampling used here:
- `subdifferentialImage`, `∂f(S)`, and `mem_subdifferentialImage` from
  `Chap05/Definition_5_24_3`;
- `directionalDerivativeAt_eq_supportFunction_subdifferentialAt` from `Chap05/Lemma_23_0_1`;
- `Function.subdifferentialAt_nonempty_of_mem_riDom`,
  `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom`, and
  `Function.directionalDerivativeAt_finite_everywhere_of_mem_interior_dom` from
  `Chap05/Theorem_23_4`.

Best owner abstraction first:
- the source set `∂f(S)` is canonically the upstream owner `subdifferentialImage f S`, i.e. the
  relation image of the dual-valued graph owner, not the Euclidean bridge graph;
- this file uses that owner only through the source-facing notation `∂f(S)`, so theorem surfaces
  avoid local alias wrappers and long owner-heavy terms.

Primitive data vs derived API:
- primitive source-facing data: the set `S` and the canonical image owner `∂f(S)`;
- derived API: nonemptiness, closedness, boundedness, the source supremum
  `sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}`, the resulting directional-derivative estimate, and the Lipschitz
  bound for `f.realBranch` on `S`.

Layer target:
- `source-facing` theorems stated directly through the `core/canonical` owner
  `∂f(S)`;
- no parallel Euclidean graph wrapper is kept as the main theorem surface.

Ambient-assumption minimization:
- the source's `R^n` is represented by an arbitrary finite-dimensional real normed space;
- the scalar remains `ℝ` here because the reused canonical owners
  `directionalDerivativeAt`, `dom(·)`, `Function.IsConvex`, `Function.IsProper`, and the
  closed-graph clause through `Function.IsClosedProperConvex` are all surfaced on
  `E → WithBotTop ℝ` in the current upstream Chapter 23/24 API;
- the codomain owner for `∂f(S)` is already pairing-parametric upstream in
  `subdifferentialImage`; this theorem specializes to `StrongDual ℝ E` only where the dual norm
  bound `sSup (norm '' ∂f(S))` is the statement's actual content.
-/

-- Proof sketch: choose `x ∈ S`. Since `S ⊆ riDom(f)`, Theorem 23.4 gives a nonempty
-- subdifferential at that point, and any of its elements belongs to the image
-- `∂f(S)`.
/-- The source set `∂f(S)` is
nonempty whenever `S` is nonempty and lies in `riDom(f)`. -/
theorem subdifferentialImage_nonempty_of_isConvex_isProper_of_subset_riDom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ riDom(f)) :
    (∂f(S)).Nonempty := sorry

/-- Intrinsic-domain source-facing form for nonemptiness of `∂f(S)`. -/
theorem subdifferentialImage_nonempty_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ riDom(f)) :
    (∂f(S)).Nonempty :=
  subdifferentialImage_nonempty_of_isConvex_isProper_of_subset_riDom
    hf_convex hf_proper hS_nonempty hS_subset

/-- Ambient-interior bridge for nonemptiness of `∂f(S)`. -/
theorem subdifferentialImage_nonempty_of_isConvex_isProper_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_nonempty : S.Nonempty) (hS_subset : S ⊆ interior (dom(f))) :
    (∂f(S)).Nonempty := by
  exact
    subdifferentialImage_nonempty_of_isConvex_isProper
      hf_convex hf_proper hS_nonempty
      (fun x hx ↦ interior_subset_intrinsicInterior (𝕜 := ℝ) (hS_subset hx))

-- Proof sketch: take a convergent sequence in `∂f(S)`. Pick
-- corresponding base points in `S`; boundedness and closedness of `S` give a convergent
-- subsequence with limit still in `S`, and Theorem 5.24.7 closes the graph of the subdifferential
-- to keep the limit dual subgradient inside the same image set.
/-- For a closed proper convex function, the source set `∂f(S)` is closed when `S` is closed,
bounded, and contained in `riDom(f)`. -/
theorem isClosed_subdifferentialImage_of_isClosedProperConvex
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ riDom(f)) :
    IsClosed (∂f(S)) := sorry

/-- Ambient-interior bridge for closedness of `∂f(S)`. -/
theorem isClosed_subdifferentialImage_of_isClosedProperConvex_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvex[ℝ] f) {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    IsClosed (∂f(S)) := by
  exact
    isClosed_subdifferentialImage_of_isClosedProperConvex
      hf hS_closed hS_bounded
      (fun x hx ↦ interior_subset_intrinsicInterior (𝕜 := ℝ) (hS_subset hx))

-- Proof sketch: for each `x ∈ S`, Theorem 23.4 gives boundedness of `subdifferentialAt f x`
-- from the interior-domain hypothesis `x ∈ interior (dom(f))`. Corollary 5.24.2 makes the
-- subdifferential map locally upper-semicontinuous on `riDom(f)`; a finite-dimensional
-- compactness argument on the closed bounded set `S` upgrades these local bounds to one global
-- bound on the image.
/-- For a proper convex function, the source set `∂f(S)` is bounded when `S` is closed,
bounded, and contained in `interior (dom(f))`. -/
theorem bounded_subdifferentialImage_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    IsBounded (∂f(S)) := sorry

/-- Companion interior-domain restatement for boundedness of `∂f(S)`. -/
theorem bounded_subdifferentialImage_of_isConvex_isProper_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    IsBounded (∂f(S)) := by
  exact
    bounded_subdifferentialImage_of_isConvex_isProper
      hf_convex hf_proper hS_closed hS_bounded hS_subset

-- Proof sketch: the canonical Chapter 23 owner theorem
-- `directionalDerivativeAt_eq_supportFunction_subdifferentialAt` identifies
-- `directionalDerivativeAt f x` with the support function of `subdifferentialAt f x` for each
-- `x ∈ S`. Since `subdifferentialAt f x` contributes to `∂f(S)`,
-- every support value is bounded above by `sup {‖x⋆‖ | x⋆ ∈ ∂f(S)} · ‖z‖` via the dual norm
-- inequality.
/-- The source constant `sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}` uniformly bounds the directional derivatives of
`f` at points of `S`. -/
theorem
    directionalDerivativeAt_le_subdifferentialImage_norm_sSup_mul_norm_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) {x : E} (hx : x ∈ S)
    (z : E) :
    directionalDerivativeAt f x z ≤
      ((sSup (norm '' (∂f(S))) * ‖z‖ : ℝ) : WithBotTop ℝ) := sorry

/-- Companion interior-domain restatement of the directional-derivative bound from `∂f(S)`. -/
theorem
    directionalDerivativeAt_le_subdifferentialImage_norm_sSup_mul_norm_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) {x : E} (hx : x ∈ S) (z : E) :
    directionalDerivativeAt f x z ≤
      ((sSup (norm '' (∂f(S))) * ‖z‖ : ℝ) : WithBotTop ℝ) := by
  exact
    directionalDerivativeAt_le_subdifferentialImage_norm_sSup_mul_norm_of_isConvex_isProper
      hf_convex hf_proper hS_closed hS_bounded hS_subset hx z

-- Proof sketch: for `x, y ∈ S`, Theorem 23.1 gives
-- `f(y) - f(x) ≥ directionalDerivativeAt f x (y - x)` and the same inequality with `x` and `y`
-- interchanged. Apply the uniform directional-derivative estimate from the previous theorem to
-- `y - x` and `x - y`, then rewrite the two-sided bound in the canonical form
-- `LipschitzOnWith ⟨sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}, _⟩ f.realBranch S`.
/-- Theorem 5.24.10: if `f` is a proper convex function and `S` is a closed bounded subset
of `interior (dom(f))`, then the source constant `α = sup {‖x⋆‖ | x⋆ ∈ ∂f(S)}` gives a
Lipschitz bound on the real branch of `f` over `S`.
The companion declarations in this file record that `∂f(S)` is nonempty when `S` is, that
`∂f(S)` is closed under `S ⊆ riDom(f)`, that `∂f(S)` is bounded under
`S ⊆ interior (dom(f))`, and that
`directionalDerivativeAt f x z ≤ α ‖z‖` for `x ∈ S`. -/
theorem
    lipschitzOnWith_subdifferentialImage_norm_sSup_realBranch_of_isConvex_isProper
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    LipschitzOnWith
      ⟨sSup (norm '' (∂f(S))),
        by
          refine Real.sSup_nonneg ?_
          rintro y ⟨xStar, hxStar, rfl⟩
          exact norm_nonneg xStar⟩
      f.realBranch S := sorry

/-- Companion interior-domain restatement of the Lipschitz estimate from Theorem 5.24.10. -/
theorem
    lipschitzOnWith_subdifferentialImage_norm_sSup_realBranch_of_subset_interior_dom
    {f : E → WithBotTop ℝ} (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    {S : Set E} (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hS_subset : S ⊆ interior (dom(f))) :
    LipschitzOnWith
      ⟨sSup (norm '' (∂f(S))),
        by
          refine Real.sSup_nonneg ?_
          rintro y ⟨xStar, _, rfl⟩
          exact norm_nonneg xStar⟩
      f.realBranch S := by
  exact
    lipschitzOnWith_subdifferentialImage_norm_sSup_realBranch_of_isConvex_isProper
      hf_convex hf_proper hS_closed hS_bounded hS_subset

end
