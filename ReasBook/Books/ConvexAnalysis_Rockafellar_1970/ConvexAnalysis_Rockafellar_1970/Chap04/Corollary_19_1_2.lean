import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_10
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_19_1

noncomputable section

open scoped BigOperators

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 19.1.2 transfers the set-level equivalence between polyhedral and
  finitely generated convex sets to convex functions through their epigraphs, and then records the
  closedness and attainment consequences.
- `core/canonical`: the owner predicates already present in the project are
  `Function.HasPolyhedralEpigraph` and `Function.HasFinitelyGeneratedConvexEpigraph`; the exact
  set-side bridge used for clause (1) is
  `Set.IsPolyhedral.isFinitelyGeneratedConvex`.
- `bridge/view`: clause (3) refers to the explicit coefficient infimum in the source-facing
  generator model `Function.pointDirectionInf`, so that attainment statement stays at the
  explicit point-and-direction level rather than introducing a second public owner wrapper.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph`;
- `Function.HasFinitelyGeneratedConvexEpigraph`;
- `Set.IsPolyhedral.isFinitelyGeneratedConvex`;
- `Function.HasFinitelyGeneratedConvexEpigraph.isFinitelyGeneratedConvex`;
- `Function.pointDirectionInf_eq_sInf`.

Primitive data vs derived API:
- primitive data for clauses (1)-(2): the function `f : E → WithTopBot 𝕜`;
- primitive data for clause (3): the finite point and direction generators for
  `Function.pointDirectionInf`, together with the explicit owner hypothesis that this generated
  function has polyhedral epigraph;
- derived owner-side API: the two owner-direction theorems
  `Function.HasPolyhedralEpigraph.hasFinitelyGeneratedConvexEpigraph` and
  `Function.HasFinitelyGeneratedConvexEpigraph.hasPolyhedralEpigraph`, together with the
  lower-semicontinuity consequence of polyhedral epigraphs;
- source-facing bridge: the equivalence
  `Function.HasPolyhedralEpigraph.iff_hasFinitelyGeneratedConvexEpigraph`.

Layer target: clauses (1)-(2) are `bridge/view` theorems between the chapter owner predicates,
while clause (3) is the source-facing attainment statement for the explicit generator model.
-/

-- Proof sketch: both function-side owner predicates are just the corresponding set-side owner
-- predicates on `epi f`. Apply the owner projections
-- `Set.IsPolyhedral.isFinitelyGeneratedConvex` and
-- `Set.IsFinitelyGeneratedConvex.isPolyhedral` directly to that intrinsic epigraph.
namespace Function.HasPolyhedralEpigraph

/-- Corollary 19.1.2 (1), canonical owner-prefix bridge form: polyhedral epigraph is equivalent
to finite generation of the intrinsic epigraph. -/
theorem iff_hasFinitelyGeneratedConvexEpigraph
    {f : E → WithTopBot 𝕜} :
    f.HasPolyhedralEpigraph ↔ f.HasFinitelyGeneratedConvexEpigraph := by
  constructor
  · intro hf
    exact hf.isPolyhedral.isFinitelyGeneratedConvex
  · intro hf
    exact hf.isFinitelyGeneratedConvex.isPolyhedral

/-- Corollary 19.1.2 (1), forward owner form: a function with polyhedral epigraph is finitely
generated. -/
theorem hasFinitelyGeneratedConvexEpigraph
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) :
    f.HasFinitelyGeneratedConvexEpigraph :=
  (iff_hasFinitelyGeneratedConvexEpigraph (f := f)).mp hf

end Function.HasPolyhedralEpigraph

namespace Function.HasFinitelyGeneratedConvexEpigraph

/-- Corollary 19.1.2 (1), canonical owner-prefix bridge form in reverse direction. -/
theorem iff_hasPolyhedralEpigraph
    {f : E → WithTopBot 𝕜} :
    f.HasFinitelyGeneratedConvexEpigraph ↔ f.HasPolyhedralEpigraph :=
  (Function.HasPolyhedralEpigraph.iff_hasFinitelyGeneratedConvexEpigraph (f := f)).symm

/-- Corollary 19.1.2 (1), reverse owner form: a finitely generated convex function has
polyhedral epigraph. -/
theorem hasPolyhedralEpigraph
    {f : E → WithTopBot 𝕜} (hf : f.HasFinitelyGeneratedConvexEpigraph) :
    f.HasPolyhedralEpigraph :=
  (iff_hasPolyhedralEpigraph (f := f)).mp hf

end Function.HasFinitelyGeneratedConvexEpigraph

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.HasPolyhedralEpigraph

-- Proof sketch: `Function.HasPolyhedralEpigraph f` says that the intrinsic epigraph `epi f`
-- is polyhedral convex. In a finite-dimensional topological module over `𝕜`, polyhedral sets are
-- closed,
-- so the intrinsic epigraph is closed; the standard epigraph criterion then gives lower
-- semicontinuity of `f`.
/-- Corollary 19.1.2 (2), canonical owner form: a function with polyhedral epigraph is closed,
expressed as lower semicontinuity. -/
theorem lowerSemicontinuous
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) :
    LowerSemicontinuous f := by
  have hclosed : IsClosed (epi f) := hf.isPolyhedral.isClosed_hasFiniteFaces.1
  exact lowerSemicontinuous_of_isClosed_epi hclosed

end Function.HasPolyhedralEpigraph

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [TopologicalSpace (WithTopBot 𝕜)]

namespace Function.HasPolyhedralEpigraph

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-- A polyhedral epigraph together with properness upgrades canonically to the Chapter 12
owner predicate `Function.IsClosedProperConvex`. -/
theorem isClosedProperConvex
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (hproper : f.IsProper) :
    IsClosedProperConvex[𝕜] f := by
  exact ⟨hf.isConvex, hproper, hf.lowerSemicontinuous⟩

/-- Primitive-data bridge: combine nonempty effective domain and pointwise `⊥`-exclusion into
`f.IsProper`, then apply the owner-level upgrade theorem. -/
theorem isClosedProperConvex_of_nonempty_dom_of_ne_bot
    {f : E → WithTopBot 𝕜} (hf : f.HasPolyhedralEpigraph) (hdom : dom(f).Nonempty)
    (hbot : ∀ x, f x ≠ ⊥) :
    IsClosedProperConvex[𝕜] f :=
  hf.isClosedProperConvex ⟨hdom, hbot⟩

end Function.HasPolyhedralEpigraph

end

section pointDirectionInf

variable {𝕜 : Type*} [CommSemiring 𝕜]
  [ConditionallyCompleteLattice 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable (points : Finset E) (pointValues : points → 𝕜)
variable (directions : Finset E) (directionValues : directions → 𝕜)

local notation "g" =>
  Function.pointDirectionInf points pointValues directions directionValues

namespace pointDirectionInf

-- Proof sketch: unfold `Function.pointDirectionInf` as an `sInf` over the admissible affine and
-- conic coefficient data, writing `g := Function.pointDirectionInf points pointValues directions
-- directionValues`. Clause (3) is stated from the primitive owner hypothesis that this generated
-- function has polyhedral epigraph. Finite value at `x` then forces an attained coefficient
-- realization of the
-- defining infimum.

/-- Corollary 19.1.2 (3), attainment at the explicit point-direction owner layer:
for the explicit point-direction generated function, under the owner hypothesis that its epigraph
is polyhedral, finite value at `x` implies that the defining infimum is attained by generating
coefficients. -/
theorem exists_generating_coefficients_of_bot_lt_and_lt_top
    {x : E}
    (hpoly : Function.HasPolyhedralEpigraph g)
    (hx : ⊥ < g x ∧ g x < ⊤) :
    ∃ pointWeights : StdSimplex 𝕜 points,
      ∃ directionWeights : directions → {a : 𝕜 // 0 ≤ a},
        x =
            pointWeights.sum (fun i a ↦ a • (i : E)) +
              ∑ j : directions, (directionWeights j : 𝕜) • (j : E) ∧
          g x =
            pointWeights.sum (fun i a ↦ ((a * pointValues i : 𝕜) : WithTopBot 𝕜)) +
              ∑ j : directions,
                (((directionWeights j : 𝕜) * directionValues j : 𝕜) : WithTopBot 𝕜) := by
  sorry

end pointDirectionInf

end pointDirectionInf

end
