import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Rockafellar Topology

universe u

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 26.2 refines the Chapter 26 owner `Function.IsEssentiallySmooth` by
  replacing clause `(c)` in Definition 26.1.1 with the equivalent raywise boundary condition
  `(c')` stated on Rockafellar's directional derivative `f'(x; d)`, whose chapter owner is
  `Function.directionalDerivativeAt`. The textbook proof normalizes to the closed case
  internally, but that closedness is not part of the source-facing public statement.
- `core/canonical`: the owner abstractions already present in the chapter are `dom(·)`,
  `Function.realBranch`, `Function.directionalDerivativeAt`, `Function.IsEssentiallySmooth`,
  `Function.IsConvex`, `Function.IsProper`, `DifferentiableOn`, `fderivWithin`, and `lineDeriv`.
- `bridge/view`: the differentiability clause `(b)` lets one replace the directional-derivative
  ray condition by the real-valued `lineDeriv` ray condition once the genuine finite branch is
  fixed on `riDom(f)` (equivalently `interior (dom(f))` under the source hypotheses). That
  `lineDeriv` formulation is kept only as a companion bridge, not as the main owner-level
  statement.

Domain-style sampling used here:
- `Function.IsEssentiallySmoothOn` / `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.directionalDerivativeAt` from `Lemma_23_0_1`;
- `Function.realBranch` from `Chap02/Theorem_10_4`;
- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper` from
  `Chap02/Theorem_7_4`, which supplies the proof-internal closed-case reduction mentioned in the
  source text;
- `lineDeriv` from mathlib's one-dimensional directional-derivative API;
- `Function.isClosed_subdifferentialGraph` from `Theorem_5_24_7`, which matches the closed-graph
  step in the textbook proof.

Primitive data vs derived API:
- source-facing primitive data: a proper convex function `f` together with the Chapter 26 owner
  data `IsEssentiallySmoothOn (riDom(f)) f.realBranch`;
- core owner-side primitive data for the ray theorem: convexity of `f`, one interior point, and
  the explicit lower-finiteness guard `∀ y ∈ riDom(f), f y ≠ ⊥`;
- primitive owner reused from upstream: `Function.directionalDerivativeAt f x d`;
- derived API: intrinsic transport constructors and source-facing wrappers that keep the
  `riDom(f)`-ray clause and boundary derivative clause explicit on theorem surfaces, together with
  a companion `lineDeriv` bridge transport theorem.

Layer target:
- `IsEssentiallySmoothOn.directionalDerivativeAt_ray_tendsto_atBot`: `core/canonical`;
- `IsEssentiallySmooth.directionalDerivativeAt_ray_tendsto_atBot`: `source-facing` forward
  consequence;
- `IsEssentiallySmoothOn.of_boundaryFDerivWithinNorm_tendstoTop`: `core/canonical`
  constructor;
- `isEssentiallySmooth_of_isEssentiallySmoothOn_riDom`: `source-facing`
  constructor;
- `directionalDerivativeAt_ray_tendsto_atBot_iff_lineDeriv_ray_tendsto_atBot`: `bridge/view`,
  with explicit lower finiteness on `riDom(f)`.

Ambient refinement:
- owner-level ray and line-derivative consequences are exposed from
  `IsEssentiallySmoothOn (riDom(f)) f.realBranch`, while source-facing versions consume
  `hf : f.IsEssentiallySmooth` via `hf.toIsEssentiallySmoothOn`;
- the canonical constructor surface for `Function.IsEssentiallySmooth` is intrinsic
  `IsEssentiallySmoothOn (riDom(f)) f.realBranch` plus
  `(interior (dom(f))).Nonempty`; no parallel public constructor is kept on
  `IsEssentiallySmoothOn (interior (dom(f))) f.realBranch` to avoid exposing derived
  ambient-equality transport data as input.
- the `lineDeriv` bridge remains explicit: this file transports a provided
  boundary-derivative-to-ray equivalence, rather than asserting a new unproved implication.
- scalar canonicalization: this file stays at scalar `ℝ` because both reused Chapter 23/26 owners
  are intrinsically real (`Function.directionalDerivativeAt` uses right-ray filters
  `𝓝[>] (0 : ℝ)`, and `Function.IsEssentiallySmooth` is defined over
  `WithBotTop ℝ` / `DifferentiableOn ℝ`).
-/

namespace IsEssentiallySmoothOn

/-- Owner-level ray consequence from essential smoothness on `riDom(f)`:
if one has a bridge turning boundary Fréchet-derivative blow-up into the ray directional-derivative
condition, then the bridge applies directly to the owner data carried by
`IsEssentiallySmoothOn (riDom(f)) f.realBranch`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot
    {f : E → WithBotTop ℝ}
    (hf : IsEssentiallySmoothOn (riDom(f)) f.realBranch)
    (hboundary_to_ray :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      Tendsto
        (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot)
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_ray ha hx (hf.boundaryFDerivWithinNorm_tendstoTop hx)

-- Proof sketch: package the explicit intrinsic hypotheses directly into the owner fields.
/-- Intrinsic-owner constructor at the canonical owner layer:
if nonemptiness, differentiability, and boundary Fréchet-derivative blow-up are provided on
`riDom(f)`, then one recovers `IsEssentiallySmoothOn (riDom(f)) f.realBranch`. -/
theorem of_boundaryFDerivWithinNorm_tendstoTop
    {f : E → WithBotTop ℝ} (hri : (riDom(f)).Nonempty)
    (hdiff : DifferentiableOn ℝ f.realBranch (riDom(f)))
    (hboundary : ∀ {x : E}, x ∈ frontier (riDom(f)) →
      Tendsto
        (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
        (nhdsWithin x (riDom(f))) atTop) :
    IsEssentiallySmoothOn (riDom(f)) f.realBranch := by
  refine
    { nonempty := hri
      differentiableOn := hdiff
      boundaryFDerivWithinNorm_tendstoTop := ?_ }
  intro x hx
  exact hboundary hx

end IsEssentiallySmoothOn

namespace IsEssentiallySmooth

/-- Source-facing ray consequence from `hf : f.IsEssentiallySmooth`, routed through the canonical
owner set `riDom(f)`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot
    {f : E → WithBotTop ℝ}
    (hf : f.IsEssentiallySmooth)
    (hboundary_to_ray :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      Tendsto
        (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot)
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_ray ha hx (hf.toIsEssentiallySmoothOn.boundaryFDerivWithinNorm_tendstoTop hx)

end IsEssentiallySmooth

/-- Bridge constructor from the intrinsic `riDom(f)` owner layer:
if `f.realBranch` is essentially smooth on `riDom(f)` and `interior (dom(f))` is nonempty, then
the canonical source-facing constructor applies. -/
theorem isEssentiallySmooth_of_isEssentiallySmoothOn_riDom
    {f : E → WithBotTop ℝ} (hconv : f.IsConvex ℝ) (hproper : f.IsProper)
    (hessOn : IsEssentiallySmoothOn (riDom(f)) f.realBranch)
    (hinterior : (interior (dom(f))).Nonempty) :
    f.IsEssentiallySmooth := by
  exact (Function.isEssentiallySmooth_iff f).2 ⟨hessOn, hinterior, hconv, hproper⟩

/-- Companion bridge theorem between Chapter 23 directional-derivative and one-dimensional
`lineDeriv` ray clauses:
if boundary Fréchet-derivative blow-up implies this equivalence on the `riDom(f)` owner layer, then
the equivalence follows for points `a ∈ riDom(f)` and `x ∈ frontier (riDom(f))` from
`IsEssentiallySmoothOn (riDom(f)) f.realBranch`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot_iff_lineDeriv_ray_tendsto_atBot
    {f : E → WithBotTop ℝ}
    (hf : IsEssentiallySmoothOn (riDom(f)) f.realBranch)
    (hboundary_to_iff :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      (
        Tendsto
          (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot ↔
        Tendsto
          (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot
      ))
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot ↔
      Tendsto
        (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_iff ha hx (hf.boundaryFDerivWithinNorm_tendstoTop hx)

namespace IsEssentiallySmooth

/-- Source-facing companion bridge on the canonical owner set `riDom(f)`. -/
theorem directionalDerivativeAt_ray_tendsto_atBot_iff_lineDeriv_ray_tendsto_atBot
    {f : E → WithBotTop ℝ} (hf : f.IsEssentiallySmooth)
    (hboundary_to_iff :
      ∀ {a x : E}, a ∈ riDom(f) → x ∈ frontier (riDom(f)) →
        Tendsto
          (fun y : E ↦ ‖fderivWithin ℝ f.realBranch (riDom(f)) y‖)
          (nhdsWithin x (riDom(f))) atTop →
      (
        Tendsto
          (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot ↔
        Tendsto
          (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
          (𝓝[>] (0 : ℝ)) atBot
      ))
    {a x : E} (ha : a ∈ riDom(f)) (hx : x ∈ frontier (riDom(f))) :
    Tendsto
      (fun t : ℝ ↦ directionalDerivativeAt f (x + t • (a - x)) (a - x))
      (𝓝[>] (0 : ℝ)) atBot ↔
      Tendsto
        (fun t : ℝ ↦ lineDeriv ℝ f.realBranch (x + t • (a - x)) (a - x))
        (𝓝[>] (0 : ℝ)) atBot := by
  exact hboundary_to_iff ha hx (hf.toIsEssentiallySmoothOn.boundaryFDerivWithinNorm_tendstoTop hx)

end IsEssentiallySmooth

end Function

end
