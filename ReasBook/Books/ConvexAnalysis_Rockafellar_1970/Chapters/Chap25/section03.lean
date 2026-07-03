import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.Monotone

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_25_3 (from Chap05) -/
noncomputable section

open scoped Topology

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.3 states that for a finite convex function on an open interval of
  `ℝ`, ordinary two-sided differentiability fails at most countably many points, and the ordinary
  derivative is continuous and nondecreasing on the intrinsic differentiability locus.
- `core/canonical`: the primitive owners for this statement are
  `DifferentiableWithinAt ℝ f I x`, `derivWithin f I x`, `Dense`, `Continuous`, `Monotone`, and
  set-theoretic countability/density owners.
- `bridge/view`: this file keeps textbook notation `D₁[f; I]` directly on the canonical
  `DifferentiableWithinAt` owner and uses open-set bridges to ordinary
  `DifferentiableAt` / `deriv` where appropriate.

Domain-style sampling used here:
- `ConvexOn ℝ I f` and one-dimensional convex derivative APIs from
  `Mathlib/Analysis/Convex/Deriv.lean`;
- countable discontinuity owners for monotone maps from
  `Mathlib/Topology/Order/Monotone.lean`.

Primitive data vs derived API:
- primitive source data: an interval carrier `I ⊆ ℝ` and a finite convex branch `f : ℝ → ℝ`;
  openness is only needed for the bridge to ordinary (`DifferentiableAt` / `deriv`) language;
- primitive owner surface: `DifferentiableWithinAt ℝ f I x` on subtype points `x : I`, exposed by
  the source notation `D₁[f; I]`;
- derived API: countability of the complement of `D₁[f; I]` in subtype form,
  density of `D₁[f; I]` in `I`, and continuity/monotonicity of
  `derivWithin f I` on that intrinsic owner.

Layer target: `source-facing`.

Abstraction audit:
- codomain/ambient layer: this source item is intentionally one-dimensional real
  (`f : ℝ → ℝ`): the mathematical content is about order-topological countability/monotonicity of
  derivatives along real intervals, and the canonical convex-derivative bridge APIs for this
  theorem layer are real-line owners. Within that layer, we keep the primary owner relative
  (`DifferentiableWithinAt` / `derivWithin`) and derive ordinary
  `DifferentiableAt`/`deriv` as open-set bridges.
- scalar/structure minimization: no extra normed/topological ambient assumptions are exposed beyond
  what `ConvexOn` on `ℝ` and relative continuity need.
- intrinsic topology/order: regularity and density are stated intrinsically on subtype points of
  `I`, using `Continuous`/`Monotone`/`Dense` rather than
  ambient `closure`/`ContinuousOn`/`MonotoneOn` phrasing.
-/

namespace Function

/-- Textbook notation for Rockafellar's Theorem 25.3 differentiability owner on `I`. -/
local notation "D₁[" f "; " I "]" =>
  (setOf (fun x : I => DifferentiableWithinAt ℝ f I x) : Set I)

@[simp] theorem mem_D₁_iff_differentiableWithinAt
    {f : ℝ → ℝ} {I : Set ℝ} {x : I} :
    x ∈ D₁[f; I] ↔ DifferentiableWithinAt ℝ f I x :=
  Iff.rfl

/-- On an open `I`, `D₁[f; I]` is exactly the ordinary differentiability locus in `I`. -/
theorem mem_D₁_iff_differentiableAt
    {f : ℝ → ℝ} {I : Set ℝ} (hI_open : IsOpen I) {x : I} :
    x ∈ D₁[f; I] ↔ DifferentiableAt ℝ f x := by
  constructor
  · intro hx
    exact hx.differentiableAt (hI_open.mem_nhds x.2)
  · intro hx
    exact hx.differentiableWithinAt

/-- On an open `I`, the relative derivative equals the ordinary derivative at every point of the
intrinsic domain subtype `I` (hence on `D₁[f; I]` in particular). -/
theorem derivWithin_eq_deriv_on_open
    {f : ℝ → ℝ} {I : Set ℝ} (hI_open : IsOpen I) :
    ∀ x : I, derivWithin f I x = deriv f x := by
  intro x
  exact derivWithin_of_isOpen hI_open x.2

/-- Theorem 25.3 (countable-exception form): for a finite convex function on an interval,
points of `I` where the relative derivative on `I` fails to exist form an at most countable subset
of the intrinsic domain type `I`, namely the complement of `D₁[f; I]`. On open `I`, this is
equivalent to failure of ordinary two-sided differentiability. -/
theorem countable_compl_D₁
    {I : Set ℝ} {f : ℝ → ℝ}
    (hf_convex : ConvexOn ℝ I f) :
    Set.Countable (D₁[f; I])ᶜ := by
  sorry

/-- Theorem 25.3 (density form): the relative differentiability set `D₁[f; I]` is dense in the
intrinsic interval domain `I`. -/
theorem dense_D₁
    {I : Set ℝ} {f : ℝ → ℝ}
    (hf_convex : ConvexOn ℝ I f) :
    Dense (D₁[f; I]) := by
  sorry

/-- Theorem 25.3 (intrinsic regularity form): on its intrinsic differentiability owner `D₁[f; I]`,
the relative derivative `derivWithin f I` is continuous and nondecreasing.
For open `I`, this recovers the ordinary-derivative formulation via
`derivWithin_eq_deriv_on_open`. -/
theorem continuous_monotone_derivWithin_on_D₁
    {I : Set ℝ} {f : ℝ → ℝ}
    (hf_convex : ConvexOn ℝ I f) :
    Continuous (fun x : D₁[f; I] ↦ derivWithin f I x) ∧
      Monotone (fun x : D₁[f; I] ↦ derivWithin f I x) := by
  sorry

end Function
