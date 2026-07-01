import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_4_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

attribute [local instance] Classical.propDecidable

section

variable {𝕜 : Type*} [DivisionRing 𝕜] [LE 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddGroup α] [ConditionallyCompleteLattice α]

open scoped Pointwise Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 8.9.5 compares the rank of a convex set with the rank of its
  indicator.
- `core/canonical`: the owner abstractions already present upstream are `Set.rank`,
  `Function.rank` on `WithBotTop α` (written source-facingly as `rank[𝕜](f)`), the
  indicator-function owner `indicator`, and the function-side lineality owner `Function.lineal`.
- `bridge/view`: the indicator function is the canonical function-side view of a set, so the
  theorem should be stated directly as an equality between the existing set-side and function-side
  rank owners, not by introducing a new packaged indicator-rank wrapper.

Domain-style sampling used here:
- `Set.rank` from Definition 8.4.6;
- `Function.rank` / notation `rank[𝕜](f)` from Definition 8.9.2;
- `indicator` and `effectiveDomain_indicator` from Definition 4.8.1;
- `Function.lineal` from Definition 8.9.0;
- `lineal_indicator_eq_lineal` from Theorem 8.7.

Primitive data vs derived API:
- primitive input: the set `C : Set E`;
- derived owner view: the function `δ[α](· | C)`;
- derived theorem-level content: the equality of the set-side and function-side rank invariants.

Layer target: `bridge/view`, preserving `Set.rank` as the set-side owner and using the indicator
owner only as the canonical function-side comparison view.
-/

namespace Set

section

variable {C : Set E}
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]

/-- Owner-level core: once the canonical bridge
`Function.lineal (δ[α](· | C)) = lin[𝕜](C)` is available, rank comparison is purely
`Set.rank`/`Function.rank` bookkeeping. -/
theorem rank_eq_rank_indicator_of_lineal_eq_lineal
    (hlineal : lin(δ[α](· | C)) = lin[𝕜](C)) :
    rank[𝕜](C) = rank[𝕜](δ[α](· | C)) := by
  letI : FiniteDimensional 𝕜 (affineSpan 𝕜 (dom((δ[α](· | C))))).direction := by
    have hdom : dom((δ[α](· | C))) = C := by
      simpa using (effectiveDomain_indicator (α := α) C)
    exact hdom.symm ▸
      (inferInstance : FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction)
  letI : FiniteDimensional 𝕜 (affineSpan 𝕜 (lin(δ[α](· | C)))).direction := by
    rw [hlineal]
    infer_instance
  have hdom : dom((δ[α](· | C))) = C := by
    simpa using (effectiveDomain_indicator (α := α) C)
  rw [Set.rank_eq, Function.rank_eq, Function.lineality_eq]
  simp [hdom, hlineal]

end

section

variable {𝕜 : Type*} [DivisionRing 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [FloorSemiring 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
variable [IsOrderedAddMonoid α]

variable {C : Set E}

variable [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (lin[𝕜](C))).direction]

/-- Theorem 8.9.5: the rank of a convex set equals the rank of its indicator. -/
theorem rank_eq_rank_indicator (hC_convex : Convex 𝕜 C) :
    rank[𝕜](C) = rank[𝕜](δ[α](· | C)) := by
  exact rank_eq_rank_indicator_of_lineal_eq_lineal
    (lineal_indicator_eq_lineal (α := α) (𝕜 := 𝕜) (C := C) hC_convex)

end

end Set

end
