

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_36_6 (from Chap07) -/
noncomputable section

universe u v w w' w''

open Function
open scoped Rockafellar

namespace Bifunction

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type w'} {XStar : Type w''}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [Sub UStar] [Neg UStar]
variable [Zero XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing UStar U 𝕜]
variable [HasPairing X XStar 𝕜]

variable (F : U → X → WithTopBot 𝕜)

local notation "L" => lagrangian (toOrderDual F)
local notation "Qual" =>
  (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 F) ∨
    (Function.HasPolyhedralEpigraph (Function.uncurry F) ∧ IsConsistent F)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 36.6 is the Kuhn--Tucker optimality criterion for the convex program
  associated with a convex bifunction `F` whose graph function is lower semicontinuous: a primal
  point `x` is optimal exactly when some dual vector `u⋆` makes the zero pair belong to the
  saddle subdifferential of the Lagrangian, and for an optimal `x` those admissible `u⋆` are
  exactly the Kuhn--Tucker vectors.
- `core/canonical`: the existing owners already present in the project are
  `(F)₀`, `IsMinOn`, `IsStronglyConsistent`, `IsConsistent`, `IsClosedConvex`,
  `Function.HasPolyhedralEpigraph (Function.uncurry F)`,
  `KT(F)`, the order-dual Lagrangian owner
  `lagrangian (toOrderDual F)`, and the saddle subdifferential notation
  `d(lagrangian (toOrderDual F) ; uStar, x)`.
- `bridge/view`: the source phrase “optimal solution of `(P)`” is rendered directly as
  `IsMinOn (F)₀ Set.univ x`, while the displayed condition
  `(0, 0) ∈ ∂L(u⋆, x)` is rendered canonically by the Chapter 35/36 owner
  `(0 : U × XStar) ∈ d(lagrangian (toOrderDual F) ; uStar, x)`.

Primary mathematical domain:
- convex duality and saddle-point optimality for generalized convex programs.

Domain-style sampling used here:
- `Bifunction.lagrangian` from `Theorem_36_5`;
- `Bifunction.isSaddlePoint_iff_zero_mem_subdifferentialAt` from
  `Proposition_36_5_2`;
- `Bifunction.IsStronglyConsistent` / `Bifunction.IsConsistent` from `Definition_6_29_10` and
  `Definition_6_29_1`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `Bifunction.IsClosedConvex` from `Defn_34_2`;
- `Bifunction.primalNormal_and_dualNormal_of_isStronglyConsistent` and
  `Bifunction.primalNormal_and_dualNormal_of_uncurry_hasPolyhedralEpigraph_and_isConsistent`
  from `Theorem_6_30_17`;
- `Bifunction.isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality` from
  `Theorem_6_30_19`;
- the Chapter 19 `HasPolyhedralEpigraph` regularity API together with the fields
  `IsClosedConvex.convex` and `IsClosedConvex.closed`, which supply the Chapter 6
  normality/duality hypotheses when needed.

Primitive data vs derived API:
- primitive source data: the bifunction `F`, the primal candidate `x`, and the dual candidate
  `uStar`;
- primitive owner-side qualification: either the Chapter 7 owner
  `IsClosedConvex F` together with strong consistency, or the polyhedral-consistent branch;
  strict consistency is omitted from the header because it already implies strong consistency by
  Definition 6.29.10, and the polyhedral branch does not keep separate closed-convex binders
  because they are derived from `HasPolyhedralEpigraph`;
- derived API: the existential optimality criterion and the fixed-`x` Kuhn--Tucker
  characterization.

Layer target: `source-facing`, stated directly on the existing owner declarations instead of
introducing a new optimal-solution package or a second Kuhn--Tucker wrapper.
-/

-- Proof sketch: first apply
-- `primalNormal_and_dualNormal_of_isStronglyConsistent` on the closed-convex/strong-consistent
-- branch or
-- `primalNormal_and_dualNormal_of_uncurry_hasPolyhedralEpigraph_and_isConsistent` on the
-- polyhedral/consistent branch to obtain primal and dual normality at `0`. Then use
-- `isDualKuhnTuckerVector_iff_isMinOn_objective_of_normality` to
-- convert primal optimality of `x` into existence of a Kuhn--Tucker vector for the adjoint
-- program, i.e. a saddle-point of `lagrangian (toOrderDual F)`. Finally rewrite that
-- saddle-point condition by `isSaddlePoint_iff_zero_mem_subdifferentialAt`.
/-- Owner-first surface of Theorem 36.6: under either the closed-convex strong-consistency
qualification (hence also under strict consistency) or the polyhedral-consistent qualification, a
point `x` is primal-optimal exactly when there exists a dual vector `u⋆` such that `(u⋆, x)` is a
saddle-point of `lagrangian (toOrderDual F)`. -/
theorem isMinOn_objective_iff_exists_isSaddlePoint_lagrangian_of_qualification
    (hqual : Qual) (x : X) :
    IsMinOn (F)₀ Set.univ x ↔
      ∃ uStar : UStar, IsSaddlePoint L uStar x := sorry

/-- Theorem 36.6: under either the closed-convex strong-consistency hypothesis (hence also under
strict consistency) or the polyhedral-consistent hypothesis, a point `x` is an optimal solution
of the convex program associated with `F` exactly when there exists a dual vector `u⋆` such that
the zero pair belongs to the saddle subdifferential of the Lagrangian at `(u⋆, x)`. -/
theorem isMinOn_objective_iff_exists_zero_mem_subdifferentialAt_lagrangian
    (hqual : Qual) (x : X) :
    IsMinOn (F)₀ Set.univ x ↔
      ∃ uStar : UStar, (0 : U × XStar) ∈ d(L ; uStar, x) := sorry

-- Proof sketch: under the same qualification, Chapter 6 gives normality and hence identifies
-- primal optimal points with Kuhn--Tucker vectors for the adjoint program. Translating that
-- normality statement through the Chapter 36 Lagrangian bridge and then applying
-- `isSaddlePoint_iff_zero_mem_subdifferentialAt` shows that, for a fixed optimal
-- primal point `x`, the admissible dual vectors are exactly those satisfying the Kuhn--Tucker
-- condition for `F`.
/-- Owner-first fixed-`x` form: for an optimal primal point `x`, dual vectors `u⋆` making
`(u⋆, x)` a saddle-point of `lagrangian (toOrderDual F)` are exactly the Kuhn--Tucker vectors,
rendered by membership in `KT(F)`. -/
theorem isSaddlePoint_lagrangian_iff_mem_kuhnTuckerVectorSet_of_isMinOn_objective
    (hqual : Qual) {x : X} (hx : IsMinOn (F)₀ Set.univ x) (uStar : UStar) :
    IsSaddlePoint L uStar x ↔ uStar ∈ KT(F) := sorry

/-- For a fixed optimal primal point `x`, the dual vectors `u⋆` satisfying
`(0, 0) ∈ d(lagrangian (toOrderDual F) ; u⋆, x)` are exactly the Kuhn--Tucker vectors of the
generalized convex program attached to `F`. -/
theorem zero_mem_subdifferentialAt_lagrangian_iff_isKuhnTuckerVector_of_isMinOn_objective
    (hqual : Qual) {x : X} (hx : IsMinOn (F)₀ Set.univ x) (uStar : UStar) :
    (0 : U × XStar) ∈ d(L ; uStar, x) ↔ uStar ∈ KT(F) := sorry

end

end Bifunction
