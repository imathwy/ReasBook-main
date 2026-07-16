import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Definition_5_3_2
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Proposition_5_3_6_1
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_1_4
import LecturesConvexOptimization_Nesterov_2018.Nesterov.Chap05.Theorem_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section FunctionalConstraintStandardFormBarrier

variable {X : Type u} {m : ℕ}

local notation "StdPoint" => ℝ × ℝ × X
local notation "PairPoint" => X × ℝ
local notation "StatePoint" => ℝ × X
local notation "PairPointL2" => WithLp 2 PairPoint
local notation "StatePointL2" => WithLp 2 StatePoint
local notation "StdPointL2" => WithLp 2 (ℝ × StatePointL2)
local notation "ofPairPoint" => (WithLp.ofLp : PairPointL2 → PairPoint)
local notation "ofStatePoint" => (WithLp.ofLp : StatePointL2 → StatePoint)
local notation "ofStdPoint" =>
  (Prod.map id ofStatePoint) ∘ (WithLp.ofLp : StdPointL2 → ℝ × StatePointL2)

/- Proposition 5.3.6.2 lies in the chapter's self-concordant-barrier / standard-form lifting
domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.add` from `Theorem_5_3_2`, the canonical barrier-sum theorem;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barriers over complete real inner-product spaces;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the source-facing strict epigraph owner
  reused by the objective and functional-constraint barrier hypotheses;
* mathlib `WithLp 2 (X × ℝ)` and `WithLp 2 (ℝ × WithLp 2 (ℝ × X))` together with `WithLp.ofLp`,
  the canonical `L²` pair/triple owners and their bridge back to the raw textbook coordinates;
* `epigraphLogBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_3_5`, the Chapter 5
  strict-epigraph barrier theorem over that owner.

Source/core/bridge triage:
* source-facing: the standard-form barrier on triples `(ξ, κ, x)`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical `L²` pair/triple owners
  `WithLp 2 (X × ℝ)` and `WithLp 2 (ℝ × WithLp 2 (ℝ × X))`;
* bridge/view: the raw-pair/raw-triple formulas transported to those owners through
  `WithLp.ofLp`.

Primitive data:
* the ambient feasible set `Q`;
* the objective and constraint functions `f₀`, `fⱼ`;
* the barrier data `FQ`, `F₀`, `Fⱼ`;
* the scalar upper bound `xiBar`.

Derived API:
* the source-facing barrier formula itself;
* its evaluation lemma;
* the standard-form barrier theorem, which consumes the canonical `L²` pair-owner barrier data on
  the strict epigraphs and realizes the standard-form owner on the canonical `L²` triple space.

This refinement therefore keeps the source-facing barrier formula and domain on the raw textbook
spaces, reuses the strict-epigraph owner from `Theorem_5_3_5` instead of restating its
set-builder, and presents the numbered theorem entirely on the canonical `WithLp.ofLp` owner
surface rather than mixing raw-pair barrier hypotheses with a separate ad hoc triple transport. -/

/-- The strict domain on which the standard-form logarithmic barrier is defined: the ambient
constraint `x ∈ Q`, the strict epigraph inequalities `f₀(x) < ξ` and `fⱼ(x) < κ`, and the two
strict slack inequalities `ξ < ξBar` and `κ < 0`. -/
def functionalConstraintStandardFormBarrierDomain
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    Set StdPoint :=
  {p | p.1 < xiBar} ∩
    {p | p.2.1 < 0} ∩
    (fun p : StdPoint ↦ p.2.2) ⁻¹' Q ∩
    (fun p : StdPoint ↦ (p.2.2, p.1)) ⁻¹'
      strictConstrainedEpigraph (Set.univ : Set X) f0 ∩
    {p | ∀ j : Fin m,
      p ∈ (fun q : StdPoint ↦ (q.2.2, q.2.1)) ⁻¹'
        strictConstrainedEpigraph (Set.univ : Set X) (fj j)}

/-- Membership in the standard-form barrier domain means that every logarithmic slack is strictly
positive and that the base point lies in `Q`. -/
@[simp] theorem mem_functionalConstraintStandardFormBarrierDomain_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ} {p : StdPoint} :
    p ∈ functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar ↔
      p.1 < xiBar ∧
        p.2.1 < 0 ∧
        p.2.2 ∈ Q ∧
        f0 p.2.2 < p.1 ∧
        ∀ j : Fin m, fj j p.2.2 < p.2.1 := by
  simp [functionalConstraintStandardFormBarrierDomain, and_assoc]

/-- Every point of the strict barrier domain is feasible for the closed standard-form
reformulation. -/
theorem functionalConstraintStandardFormBarrierDomain_subset_feasibleSet
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar ⊆
      (functionalConstraintStandardFormProblem Q f0 fj xiBar).feasibleSet := by
  intro p hp
  rcases mem_functionalConstraintStandardFormBarrierDomain_iff.mp hp with
    ⟨hxi, hkappa, hxQ, hf0, hfj⟩
  exact mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mpr
    ⟨le_of_lt hxi, le_of_lt hkappa, hxQ, le_of_lt hf0, fun j ↦ le_of_lt (hfj j)⟩

/-- The explicit barrier obtained by adding the barrier on `Q`, the epigraph barrier for the
objective, the epigraph barriers for the functional constraints, and the two logarithmic slack
terms for `ξ < ξBar` and `κ < 0`. -/
def functionalConstraintStandardFormBarrier
    (FQ : X → ℝ) (F0 : X × ℝ → ℝ) (Fj : Fin m → X × ℝ → ℝ) (xiBar : ℝ) :
    StdPoint → ℝ :=
  fun p ↦
    FQ p.2.2 +
      F0 (p.2.2, p.1) +
        (∑ j : Fin m, Fj j (p.2.2, p.2.1)) +
          sublevelLogBarrier (fun q : StdPoint ↦ q.1) xiBar p +
            sublevelLogBarrier (fun q : StdPoint ↦ q.2.1) 0 p

/-- Evaluating `functionalConstraintStandardFormBarrier` reproduces the textbook barrier formula
`F_Q(x) + F₀(x, ξ) + ∑ⱼ Fⱼ(x, κ) - log (ξBar - ξ) - log (-κ)`. -/
@[simp]
theorem functionalConstraintStandardFormBarrier_apply
    (FQ : X → ℝ) (F0 : X × ℝ → ℝ) (Fj : Fin m → X × ℝ → ℝ) (xiBar : ℝ)
    (p : StdPoint) :
    functionalConstraintStandardFormBarrier FQ F0 Fj xiBar p =
      FQ p.2.2 +
        F0 (p.2.2, p.1) +
          (∑ j : Fin m, Fj j (p.2.2, p.2.1)) -
            Real.log (xiBar - p.1) - Real.log (-p.2.1) := by
  simp [functionalConstraintStandardFormBarrier, sublevelLogBarrier, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

-- Proof sketch: view each summand as a self-concordant barrier on the reformulated feasible set:
-- `FQ` is pulled back along the coordinate projection `(ξ, κ, x) ↦ x`, `F₀` is pulled back
-- along `(ξ, κ, x) ↦ (x, ξ)`, and each `Fⱼ` is pulled back along `(ξ, κ, x) ↦ (x, κ)` using the
-- canonical owner theorem `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`. The two
-- logarithmic
-- slack terms are the standard one-dimensional barriers pulled back from `x ↦ -log x`. Repeated
-- application of `IsSelfConcordantBarrierOnWith.add` then yields the parameter sum
-- `vQ + v₀ + ∑ⱼ vⱼ + 2`.
/-- Proposition 5.3.6.2: if `F_Q` is a self-concordant barrier for `Q`, if `F₀` is a
self-concordant barrier on the canonical `L²` pair owner over the strict epigraph of `f₀`, and
if each `Fⱼ` is a self-concordant barrier on the canonical `L²` pair owner over the strict
epigraph of `fⱼ`, then
`F_Q(x) + F₀(x, ξ) + ∑ⱼ Fⱼ(x, κ) - log (ξBar - ξ) - log (-κ)` is a self-concordant barrier for
the strict reformulated barrier domain `ξ < ξBar`, `κ < 0`, `x ∈ Q`, `f₀(x) < ξ`, `fⱼ(x) < κ`,
which sits inside the closed feasible set of Proposition `5.3.6.1`, with parameter
`v_Q + v₀ + ∑ⱼ vⱼ + 2`, all viewed on the canonical `L²` owners through `WithLp.ofLp`. -/
theorem functionalConstraintStandardFormBarrier_isSelfConcordantBarrierOnWith
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ}
    {FQ : X → ℝ} {F0 : X × ℝ → ℝ} {Fj : Fin m → X × ℝ → ℝ}
    {xiBar : ℝ} {vQ v0 : NNReal} {vj : Fin m → NNReal}
    (hFQ : IsSelfConcordantBarrierOnWith Q vQ FQ)
    (hF0 : IsSelfConcordantBarrierOnWith
      (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) f0)
      v0 (F0 ∘ ofPairPoint))
    (hFj : ∀ j : Fin m,
      IsSelfConcordantBarrierOnWith
        (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) (fj j))
        (vj j) (Fj j ∘ ofPairPoint)) :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹'
        functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar)
      (vQ + v0 + (∑ j : Fin m, vj j) + 2)
      (functionalConstraintStandardFormBarrier FQ F0 Fj xiBar ∘ ofStdPoint) := sorry

end FunctionalConstraintStandardFormBarrier
