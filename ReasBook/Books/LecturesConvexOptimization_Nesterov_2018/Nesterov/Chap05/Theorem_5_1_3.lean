import Mathlib
import LecturesConvexOptimization_Nesterov_2018.Chap01.Definition_1_10_18
import LecturesConvexOptimization_Nesterov_2018.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter Set Topology
open scoped Topology

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 5.1.3 lies in the self-concordance / barrier-function domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` from `Definition_5_1_1`, the chapter owner for self-concordance on an
  open convex domain;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the canonical barrier owner on a closed
  feasible set via a bundled map on its interior;
* `liftedConeLogSumExpBarrier_restriction_isBarrierFunctionOn` from `Chap05/Theorem_5_4_7_7`,
  showing the same frontier-blow-up property on a relative ambient space via the canonical owner
  `IsBarrierFunctionOn`.

Best owner abstraction:
* source-facing input: `IsSelfConcordantOnWith dom Mf f`, with `IsSelfConcordantOn dom f` kept for
  the purely propositional companion consequence;
* core/canonical output: `IsBarrierFunctionOn (closure dom) F`, where `F` is the canonical
  restriction of `f` to `interior (closure dom) = dom`;
* bridge/view: the displayed `Tendsto` statement for sequences in `dom`.

Primitive data:
* the self-concordance-with-constant hypothesis on `dom`;
* nonemptiness of the open domain, needed only for the barrier-owner theorem, not for the
  restricted owner map itself.

Derived API:
* the restricted continuous owner map `hself.toBarrierMap`;
* the sequence-level frontier blow-up statement as a consequence of the barrier owner.
-/

namespace IsSelfConcordantOnWith

/-- On a self-concordant domain, taking interior after closure recovers the original domain. -/
theorem interior_closure_eq
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) :
    interior (closure dom) = dom := by
  by_cases hdom : dom.Nonempty
  · have hinterior : (interior dom).Nonempty := by
      simpa [hself.isOpen_domain.interior_eq] using hdom
    calc
      interior (closure dom) = interior dom :=
        hself.convex_domain.interior_closure_eq_interior_of_nonempty_interior hinterior
      _ = dom := hself.isOpen_domain.interior_eq
  · simp [Set.not_nonempty_iff_eq_empty.mp hdom]

/-- The canonical bundled owner map of a self-concordant function on the intrinsic barrier domain
`interior (closure dom) = dom`. -/
abbrev toBarrierMap
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) :
    C(interior (closure dom), ℝ) :=
  let hcont : ContinuousOn f (interior (closure dom)) := by
    simpa [hself.interior_closure_eq] using hself.contDiffOn.continuousOn
  { toFun := (interior (closure dom)).restrict f
    continuous_toFun := hcont.restrict }

/-- Theorem 5.1.3: a self-concordant function on a nonempty open convex domain is a barrier for
that domain in the canonical closed-set owner sense, namely for `closure dom` with owner map given
by restricting `f` to `interior (closure dom) = dom`. The self-concordance constant is explicit in
the hypothesis only so the bundled owner map can remain canonical without introducing a public
choice-based definition from the existential abbreviation `IsSelfConcordantOn`. -/
-- Proof sketch: the self-concordance hypothesis already packages openness, convexity, and `C³`
-- regularity on `dom`, hence continuity on `dom`. For a nonempty open convex set in finite
-- dimension, `interior (closure dom) = dom`, so `f` canonically defines a bundled continuous map
-- on `interior (closure dom)`. The textbook boundary blow-up statement is then exactly the barrier
-- axiom on `closure dom`.
theorem isBarrierFunctionOn
    {dom : Set E} {Mf : NNReal} {f : E → ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f) (hdom : dom.Nonempty) :
    IsBarrierFunctionOn (closure dom) hself.toBarrierMap := sorry

end IsSelfConcordantOnWith

namespace IsSelfConcordantOn

/-- Companion consequence of Theorem 5.1.3: along any sequence in `dom` converging to a frontier
point of `dom`, the function values tend to `+∞`. -/
theorem tendsto_atTop_of_tendsto_frontier
    {dom : Set E} {f : E → ℝ} (hself : IsSelfConcordantOn dom f) (x : ℕ → dom) {xBar : E}
    (hx : Tendsto (fun k ↦ (x k : E)) atTop (𝓝 xBar))
    (hxBar : xBar ∈ frontier dom) :
    Tendsto (fun k ↦ f (x k)) atTop atTop := by
  rcases hself with ⟨Mf, hMf⟩
  let xClosure : ℕ → interior (closure dom) :=
    fun k ↦ ⟨x k, by simp [hMf.interior_closure_eq]⟩
  have hdom : dom.Nonempty := ⟨x 0, (x 0).property⟩
  have hxBarClosure : xBar ∈ frontier (closure dom) := by
    simpa [frontier, closure_closure, hMf.interior_closure_eq, hMf.isOpen_domain.interior_eq] using
      hxBar
  have hbarrier : IsBarrierFunctionOn (closure dom) hMf.toBarrierMap :=
    hMf.isBarrierFunctionOn hdom
  simpa [IsSelfConcordantOnWith.toBarrierMap, xClosure] using
    hbarrier.tendsTo_atTop_of_tendsto_frontier xClosure hx hxBarClosure

end IsSelfConcordantOn
