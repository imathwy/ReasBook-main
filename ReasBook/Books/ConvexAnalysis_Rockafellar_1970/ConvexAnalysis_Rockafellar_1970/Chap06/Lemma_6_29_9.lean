import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_10

noncomputable section

universe u v w

open scoped Rockafellar

namespace OrdinaryConvexProgram

section

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Ring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable [AddCommGroup β] [PartialOrder β] [Module 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.9 is the Slater-style characterization of strong consistency for an
  ordinary convex program.
- `core/canonical`: the Chapter 6 owner for strong consistency is
  `Bifunction.IsStronglyConsistent 𝕜`, applied here to the associated perturbation owner
  `P.perturbedProblem`.
- `bridge/view`: the source witness is still a point of `ri[𝕜](P.constraintSet)` with strict
  inequalities and exact equalities, written intrinsically on the program's inequality/equality
  index owners.

Domain-style sampling used here:
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `Bifunction.IsStronglyConsistent` from `Definition_6_29_10`;
- `Bifunction.dom` / `Bifunction.mem_dom_iff_exists` from `Definition_6_29_8`;
- the chapter notation `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive source data: the program `P`;
- canonical owner-side predicate: strong consistency of `P.perturbedProblem`;
- source-facing witness owner: `P.HasRiStrictFeasiblePoint`;
- derived bridge view: the corresponding explicit existential witness on `P.constraintSet`.

Layer target: `source-facing`, stated on the existing owners `P.perturbedProblem`, `ri[𝕜](·)`,
and the ordinary-program owner `P.HasRiStrictFeasiblePoint`.
-/

-- Proof sketch: this is the definitional source-facing owner packaging of the relative-interior
-- strict feasible witness.
/-- Source-facing owner for the relative-interior strict-feasibility witness of `P`: a point of
`P.constraintSet` that lies in `ri[𝕜](P.constraintSet)`, satisfies every inequality strictly, and
satisfies every equality exactly. -/
def HasRiStrictFeasiblePoint : Prop :=
  ∃ x : P.constraintSet,
    (x : E) ∈ ri[𝕜](P.constraintSet) ∧
      (∀ i, P.inequality i x < 0) ∧
      (∀ j, P.equality j x = 0)

-- Proof sketch: expand the witness owner definition.
/-- Bridge expansion: `P.HasRiStrictFeasiblePoint` is exactly the explicit relative-interior
strict-feasible witness surface. -/
theorem hasRiStrictFeasiblePoint_iff :
    P.HasRiStrictFeasiblePoint ↔
      ∃ x : P.constraintSet,
        (x : E) ∈ ri[𝕜](P.constraintSet) ∧
          (∀ i, P.inequality i x < 0) ∧
          (∀ j, P.equality j x = 0) :=
  Iff.rfl

-- Proof sketch: unfold `Bifunction.IsStronglyConsistent` for `P.perturbedProblem`. Via
-- `Bifunction.dom` and `P.mem_perturbedFeasibleSet`, a perturbation parameter lies in the domain
-- exactly when some point of `P.constraintSet` satisfies the corresponding inequality and
-- equality bounds. Specializing the relative-interior condition at the zero perturbation yields
-- precisely a point of `P.constraintSet` lying in `ri[𝕜](P.constraintSet)` with strict
-- inequalities and exact equalities.
variable [TopologicalSpace β]

/-- Lemma 6.29.9, owner form: the perturbation problem attached to an ordinary convex program is
strongly consistent exactly when `P` has a relative-interior strict feasible point. -/
theorem stronglyConsistent_iff_hasRiStrictFeasiblePoint :
    Bifunction.IsStronglyConsistent 𝕜 P.perturbedProblem ↔
      P.HasRiStrictFeasiblePoint := by
  -- The source-facing bridge proof is deferred in this canonicalization pass; this item now
  -- exposes the intended owner-level theorem surface directly.
  sorry

-- Proof sketch: unfold `P.HasRiStrictFeasiblePoint`.
/-- Lemma 6.29.9, explicit witness form: strong consistency is equivalent to existence of a
relative-interior strict feasible point of `P.constraintSet`. -/
theorem stronglyConsistent_iff_exists_ri_strict_feasible_point :
    Bifunction.IsStronglyConsistent 𝕜 P.perturbedProblem ↔
      ∃ x : P.constraintSet,
        (x : E) ∈ ri[𝕜](P.constraintSet) ∧
          (∀ i, P.inequality i x < 0) ∧
          (∀ j, P.equality j x = 0) := by
  simpa [HasRiStrictFeasiblePoint] using
    (stronglyConsistent_iff_hasRiStrictFeasiblePoint (𝕜 := 𝕜) (P := P))

end

end OrdinaryConvexProgram
