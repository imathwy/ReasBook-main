import Mathlib
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_5_3_0_1 (from Chap05) -/
universe u

/- Definition 5.3.0.1 is a recall-only item in the chapter's self-concordance domain.

Primary domain:
- self-concordant functions on an open convex domain in a real inner-product space.

Sampled owner-style declarations:
- `IsSelfConcordantOnWith` from `Definition_5_1_1`, the quantitative owner carrying the constant
  `M_f`;
- `IsSelfConcordantOn` from `Definition_5_1_1`, the existential source-facing relaxation;
- `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the canonical owner for the case
  `M_f = 1`;
- the definitional equality
  `IsStandardSelfConcordantOn dom f = IsSelfConcordantOnWith dom 1 f`.

Best owner abstraction:
- source-facing: standard self-concordance on `dom`;
- core/canonical: `IsStandardSelfConcordantOn dom f`;
- bridge/view: the definitional equality with `IsSelfConcordantOnWith dom 1 f`.

Primitive data:
- none; this item only recalls an existing owner.

Derived API:
- the owner predicate `IsStandardSelfConcordantOn`;
- the definitional equality with `IsSelfConcordantOnWith dom 1 f`.

This file therefore keeps no parallel local predicate for “self-concordant with constant `1`”.
It recalls the upstream owner from `Definition_5_1_1` directly, and the textbook specification is
checked by definitional equality instead of a redundant wrapper theorem. -/

/- Definition 5.3.0.1 recalls the canonical owner for standard self-concordance. -/
recall IsStandardSelfConcordantOn

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (dom : Set E) (f : E → ℝ)

/- The textbook phrase “exactly a self-concordant function with constant `M_f = 1`” is
definitionally the Chapter 5 owner specialized to `1`. -/
#check (Iff.rfl : IsStandardSelfConcordantOn dom f ↔ IsSelfConcordantOnWith dom 1 f)

end

/-! ### Definition_5_3_0_2 (from Chap05) -/
universe u

/- Definition 5.3.0.2 lies in the chapter's `WithTop ℝ` convex-analysis domain.

Sampled owner-style declarations:
- `withTopEffectiveDomain` / `dom` from `Chap03/Definition_3_3`
- `extendedRealEffectiveDomain` / `dom` from `Chap03/Definition_3_1_1_2`
- mathlib `closure`

Best owner abstraction:
- source-facing: the textbook notation `Dom f`
- core/canonical: `closure (dom f)`
- bridge/view: the scoped notation declaration below

Primitive data:
- the effective domain owner `dom f`
- the topological closure operator

Derived API:
- `mem_Dom_iff`
- `dom_subset_Dom`

This item is only a source-facing notation bridge. Since `closure (dom f)` is already the exact
canonical owner, the refinement keeps no parallel alias for it and exposes only the notation and
its atomic bridge lemmas. -/

/-- Textbook notation for the closed effective domain of an `ℝ ∪ {+∞}`-valued function. -/
scoped[WithTopConvexAnalysis] notation "Dom " f:arg => closure (withTopEffectiveDomain f)

open scoped WithTopConvexAnalysis

/-- Membership in `Dom f` means membership in the closure of the effective domain. -/
@[simp] theorem mem_Dom_iff {X : Type u} [TopologicalSpace X]
    {f : X → WithTop ℝ} {x : X} :
    x ∈ Dom f ↔ x ∈ closure (dom f) :=
  Iff.rfl

/-- The effective domain is contained in its closed effective domain. -/
theorem dom_subset_Dom {X : Type u}
    [TopologicalSpace X] (f : X → WithTop ℝ) :
    dom f ⊆ Dom f := by
  simpa using (subset_closure : dom f ⊆ closure (dom f))

/-! ### Corollary_5_3_1 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "Z" => WithLp 2 (E × ℝ)
local notation "ofZ" => (WithLp.ofLp : Z → E × ℝ)

-- Proof sketch: repeat the self-concordance part of Theorem 5.3.5 on the canonical `L²`
-- product owner `Z = WithLp 2 (E × ℝ)`, using the canonical raw-pair bridge `ofZ`. View
-- `z ↦ f (ofZ z).1` as the affine pullback of `f` along the first projection, and view
-- `z ↦ -log ((ofZ z).2 - f (ofZ z).1)` as the logarithmic barrier term for the strict epigraph
-- inequality. The affine-precomposition theorem, the logarithmic-barrier theorem, and the sum
-- theorem yield standard self-concordance on the pulled-back strict epigraph domain, and this
-- argument does not use the barrier-parameter inequality for `f`.
/-- Corollary 5.3.1: if `f` is a standard self-concordant function on `dom`, then the epigraph
barrier, viewed on the canonical `L²` product owner `WithLp 2 (E × ℝ)` through `ofZ`, is also
standard self-concordant on the strict epigraph domain from Theorem 5.3.5. -/
theorem epigraphLogBarrier_isStandardSelfConcordantOn
    {dom : Set E} {f : E → ℝ}
    (h : IsStandardSelfConcordantOn dom f) :
    IsStandardSelfConcordantOn
      (ofZ ⁻¹' strictConstrainedEpigraph dom f)
      (epigraphLogBarrier f ∘ ofZ) := sorry

end

/-! ### Definition_5_3_1 (from Chap05) -/
universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.3.1 lies in the constrained barrier / path-following domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with its objective;
- `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the Chapter 5 owner for a standard
  self-concordant potential on an open convex domain;
- `IsSelfConcordantOnWith.isBarrierFunctionOn` in `Theorem_5_1_3`, the canonical bridge turning
  self-concordance on `dom` into a barrier on `closure dom`;
- `SetConstrainedMinimizationProblem` in `Chap03/Definition_3_36`, where the chapter keeps the
  constrained problem at the owner level instead of introducing a parallel wrapper.

Best owner abstraction:
- source-facing data: a domain `dom`, an objective vector `c`, and a standard self-concordant
  potential `F` on `dom`;
- core/canonical ambient owner:
  `SetConstrainedMinimizationProblem E` with feasible set `closure dom` and objective `inner ℝ c`;
- bridge/view: the Chapter 5 regularity/barrier hypothesis `IsStandardSelfConcordantOn dom F`.

Primitive data:
- the ambient constrained problem owner on `closure dom` with linear objective `inner ℝ c`;
- the barrier-side hypothesis `IsStandardSelfConcordantOn dom F`.

Derived API:
- openness and convexity of `dom`, recovered from `IsStandardSelfConcordantOn dom F`;
- closedness of the feasible set `closure dom`;
- later barrier facts on `closure dom`, derived through `Theorem_5_1_3`.

Source/core/bridge triage:
- source-facing: the textbook triple `(dom, c, F)`;
- core/canonical: `SetConstrainedMinimizationProblem E`;
- bridge/view: `IsStandardSelfConcordantOn dom F` and its barrier consequences on `closure dom`.

This file therefore keeps no parallel `StandardConstrainedMinimizationProblem` wrapper. The
constrained problem is the existing owner `SetConstrainedMinimizationProblem`, and the Chapter 5
barrier data remain separate owner-level hypotheses. -/

section

variable (dom : Set E) (c : E) (F : E → ℝ)

/- Definition 5.3.1 uses the existing constrained-problem owner together with the existing
Chapter 5 standard self-concordance owner. -/
recall SetConstrainedMinimizationProblem
recall IsStandardSelfConcordantOn

set_option linter.hashCommand false in
#check
  (.mk (closure dom) (inner ℝ c) : SetConstrainedMinimizationProblem E)

set_option linter.hashCommand false in
#check (IsStandardSelfConcordantOn dom F)

end

/-! ### Definition_5_3_1_1 (from Chap05) -/
universe u

/- Definition 5.3.1.1 is a source-facing recall in the chapter's central-path / interior-point
domain.

Primary domain:
- central paths for barrier-penalized linear minimization on a feasible set in a real
  inner-product space.

Sampled owner-style declarations:
- `centralPathPenaltyObjective` in `Definition_5_3_6_1`, the chapter owner for the penalty
  objective `x ↦ t ⟪c, x⟫ + F x`;
- `centralPathPenaltyObjective_apply`, the defining evaluation theorem for that owner;
- `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner predicate for central paths;
- `isCentralPath_iff`, the companion pointwise minimizer expansion on the canonical `IsMinOn`
  owner.

Best owner abstraction:
- source-facing/core: `centralPathPenaltyObjective` and `IsCentralPath`;
- bridge/view: `centralPathPenaltyObjective_apply` and `isCentralPath_iff`.

Primitive data:
- `dom : Set E`
- `c : E`
- `f : E → ℝ`
- `xStar : Set.Ici (0 : ℝ) → dom`

Derived API:
- the penalty formula
  `centralPathPenaltyObjective c f t x = (t : ℝ) * inner ℝ c x + f x`;
- the pointwise minimizer expansion of `IsCentralPath dom c f xStar`.

Source/core/bridge triage:
- source-facing: the textbook penalty objective and central-path predicate of Definition 5.3.1.1;
- core/canonical: the existing Chapter 5 owner declarations in `Definition_5_3_6_1`;
- bridge/view: the evaluation and `iff` companion theorems.

The previous version duplicated those owner declarations verbatim, creating a second public copy
of the same central-path surface. This file now recalls the existing owner declarations directly
instead of maintaining parallel local definitions. -/

recall centralPathPenaltyObjective
recall centralPathPenaltyObjective_apply
recall IsCentralPath
recall isCentralPath_iff

/-! ### Example_5_3_1_1 (from Chap05) -/
open scoped Gradient

noncomputable section

/- Example 5.3.1.1 lies in the Chapter 5 self-concordant-barrier / affine-objective domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrier_parameter_bound`, the primitive owner inequality used to
  contradict barrierhood on `Set.univ`;
* `quadraticAffineObjective` in `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives;
* `quadraticAffineObjective_gradient_eq` and `quadraticAffineObjective_hessian_eq`, the canonical
  differential API for that owner.

Best owner abstraction:
* source-facing: the scalar affine function `x ↦ α + a x`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: the zero-Hessian specialization
  `quadraticAffineObjective α a (0 : ℝ →L[ℝ] ℝ)`.

Primitive data:
* the scalar offset `α`;
* the nonzero slope `a`;
* the barrier parameter `ν`.

Derived API:
* the affine-quadratic owner view of `x ↦ α + a x`;
* the constant gradient formula `∇f(x) = a`;
* the vanishing Hessian formula `∇²f(x) = 0`.

This refinement keeps the theorem source-facing, but removes the ad hoc differential computation
route in favor of the existing affine-quadratic owner and the primitive barrier-owner inequality. -/

-- Proof sketch: if `f x = α + a * x` were a `ν`-self-concordant barrier on `ℝ`, then the
-- barrier-parameter inequality from `IsSelfConcordantBarrierOnWith` would read `2 * a * u ≤ ν`
-- for every direction `u : ℝ` because the Hessian vanishes identically. Taking `u` with the same
-- sign as `a` and arbitrarily large magnitude contradicts this when `a ≠ 0`.
/-- Example 5.3.1.1: the affine function `x ↦ α + a x` on all of `ℝ` is not a
`ν`-self-concordant barrier whenever `a ≠ 0`. In particular, the nonconstant linear
specialization `x ↦ a x` cannot be a self-concordant barrier because its Hessian is zero. -/
theorem affineFunction_not_isSelfConcordantBarrierOnWith
    (α a : ℝ) (ν : NNReal) (ha : a ≠ 0) :
    ¬ IsSelfConcordantBarrierOnWith (Set.univ : Set ℝ) ν (fun x : ℝ ↦ α + a * x) := by
  intro h
  let A : ℝ →L[ℝ] ℝ := 0
  have hzero : quadraticAffineObjective α a A = fun x : ℝ ↦ α + inner ℝ a x := by
    exact quadraticAffineObjective_zero_operator α a
  have hobj : quadraticAffineObjective α a A = fun x : ℝ ↦ α + a * x := by
    calc
      quadraticAffineObjective α a A = fun x : ℝ ↦ α + inner ℝ a x := hzero
      _ = fun x : ℝ ↦ α + a * x := by
        funext x
        have hinner : inner ℝ a x = x * a := RCLike.inner_apply a x
        calc
          α + inner ℝ a x = α + x * a := by rw [hinner]
          _ = α + a * x := by ring
  have hbarrier :
      IsSelfConcordantBarrierOnWith (Set.univ : Set ℝ) ν (quadraticAffineObjective α a A) := by
    simpa [hobj] using h
  let u : ℝ := ((ν : ℝ) + 1) / a
  have hbound := hbarrier.barrier_parameter_bound
    (show (0 : ℝ) ∈ (Set.univ : Set ℝ) by simp) u
  have hA : IsSelfAdjoint A :=
    ContinuousLinearMap.isPositive_zero.isSelfAdjoint
  have hgrad : ∇ (quadraticAffineObjective α a A) 0 = a := by
    simpa [A] using congrFun (quadraticAffineObjective_gradient_eq α a A hA) 0
  have hhess : hessian (quadraticAffineObjective α a A) 0 = A := by
    simpa using quadraticAffineObjective_hessian_eq α a A hA 0
  have hu : a * u = (ν : ℝ) + 1 := by
    dsimp [u]
    field_simp [ha]
  have hcontr : 2 * ((ν : ℝ) + 1) ≤ (ν : ℝ) := by
    calc
      2 * ((ν : ℝ) + 1) =
          2 * inner ℝ (∇ (quadraticAffineObjective α a A) 0) u -
            inner ℝ u (hessian (quadraticAffineObjective α a A) 0 u) := by
        rw [hgrad, hhess]
        have hinner : inner ℝ a u = u * a := RCLike.inner_apply a u
        have hau : inner ℝ a u = (ν : ℝ) + 1 := by
          calc
            inner ℝ a u = u * a := hinner
            _ = a * u := by ring
            _ = (ν : ℝ) + 1 := hu
        simp [A, hau]
      _ ≤ (ν : ℝ) := hbound
  linarith

end

/-! ### Example_5_3_1_2 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 5.3.1.2 lies in the Chapter 5 self-concordant-barrier / quadratic-objective domain.

Sampled owner-style declarations in this domain:
* `quadraticAffineObjective` together with `quadraticAffineObjective_hessian_eq` in
  `Example_5_1_2`, the source-facing owner and its canonical Hessian API for affine-quadratic
  objectives;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for `ν`-self-
  concordant barriers;
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the chapter owner for positive-definite
  Hessians on a domain;
* `selfAdjointPart` in mathlib, the canonical projection from an operator to its self-adjoint
  part.

Best owner abstraction:
* source-facing: the affine-quadratic objective `quadraticAffineObjective α a A`;
* core/canonical: `IsSelfConcordantBarrierOnWith` and `HasPositiveDefiniteHessianOn`;
* bridge/view: passage from `A` to the canonical mathlib owner `selfAdjointPart ℝ A`, which
  preserves both the quadratic-affine objective and the quadratic form `u ↦ ⟪u, A u⟫`.

Primitive data:
* the scalar offset `α`;
* the linear coefficient `a`;
* the bounded operator `A`;
* strict positivity of the quadratic form `u ↦ ⟪u, A u⟫` on nonzero directions.

Derived API:
* the self-adjoint part `selfAdjointPart ℝ A`, which is the actual Hessian owner of the quadratic
  objective;
* positive definiteness of the Hessian of `quadraticAffineObjective α a A` on `Set.univ`;
* the barrier contradiction obtained from the owner inequality on `Set.univ`.

This refinement keeps the example source-facing, but removes the redundant self-adjointness binder
from the main theorems and reuses the existing Chapter 5 Hessian-positivity owner after passing to
the canonical self-adjoint part of the quadratic operator. -/

variable [CompleteSpace E]

/-- Passing to `selfAdjointPart ℝ A` does not change the quadratic term `⟪A x, x⟫`. -/
theorem selfAdjointPart_apply_inner_eq (A : E →L[ℝ] E) (x : E) :
    inner ℝ ((selfAdjointPart ℝ A : E →L[ℝ] E) x) x = inner ℝ (A x) x := by
  rw [show (selfAdjointPart ℝ A : E →L[ℝ] E) = (⅟2 : ℝ) • (A + A.adjoint) by
    rw [selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint]]
  calc
    inner ℝ (((⅟2 : ℝ) • (A + A.adjoint)) x) x
        = (⅟2 : ℝ) * inner ℝ (A x) x + (⅟2 : ℝ) * inner ℝ (A.adjoint x) x := by
            simp [inner_add_left, inner_smul_left]
    _ = (⅟2 : ℝ) * inner ℝ (A x) x + (⅟2 : ℝ) * inner ℝ (A x) x := by
          rw [ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
    _ = inner ℝ (A x) x := by
          have htwo : (⅟2 : ℝ) * 2 = 1 := by norm_num
          calc
            (⅟2 : ℝ) * inner ℝ (A x) x + (⅟2 : ℝ) * inner ℝ (A x) x
                = ((⅟2 : ℝ) * 2) * inner ℝ (A x) x := by ring
            _ = inner ℝ (A x) x := by rw [htwo, one_mul]

/-- Passing to `selfAdjointPart ℝ A` does not change the quadratic form `u ↦ ⟪u, A u⟫`. -/
theorem inner_selfAdjointPart_apply_eq (A : E →L[ℝ] E) (u : E) :
    inner ℝ u ((selfAdjointPart ℝ A : E →L[ℝ] E) u) = inner ℝ u (A u) := by
  rw [show (selfAdjointPart ℝ A : E →L[ℝ] E) = (⅟2 : ℝ) • (A + A.adjoint) by
    rw [selfAdjointPart_apply_coe, ContinuousLinearMap.star_eq_adjoint]]
  calc
    inner ℝ u (((⅟2 : ℝ) • (A + A.adjoint)) u)
        = (⅟2 : ℝ) * inner ℝ u (A u) + (⅟2 : ℝ) * inner ℝ u (A.adjoint u) := by
            simp [inner_add_right, inner_smul_right]
    _ = (⅟2 : ℝ) * inner ℝ u (A u) + (⅟2 : ℝ) * inner ℝ u (A u) := by
          rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]
    _ = inner ℝ u (A u) := by
          have htwo : (⅟2 : ℝ) * 2 = 1 := by norm_num
          calc
            (⅟2 : ℝ) * inner ℝ u (A u) + (⅟2 : ℝ) * inner ℝ u (A u)
                = ((⅟2 : ℝ) * 2) * inner ℝ u (A u) := by ring
            _ = inner ℝ u (A u) := by rw [htwo, one_mul]

/-- Passing to `selfAdjointPart ℝ A` does not change the affine-quadratic objective. -/
theorem quadraticAffineObjective_selfAdjointPart_eq (α : ℝ) (a : E) (A : E →L[ℝ] E) :
    quadraticAffineObjective α a A = quadraticAffineObjective α a (selfAdjointPart ℝ A) := by
  ext x
  rw [quadraticAffineObjective, quadraticAffineObjective, selfAdjointPart_apply_inner_eq]

-- Proof sketch: replace `A` by its self-adjoint part `S := selfAdjointPart ℝ A`. The quadratic
-- objective and the quadratic form `u ↦ inner ℝ u (A u)` are unchanged by this replacement,
-- while `S` is self-adjoint. The constant-Hessian formula for `quadraticAffineObjective α a S`
-- then identifies the Hessian with `S`, so the strict positivity hypothesis transfers pointwise
-- to all Hessian quadratic forms on `Set.univ`.
/-- If the quadratic form `u ↦ ⟪u, A u⟫` is strictly positive on nonzero directions, then the
quadratic-affine objective `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` has positive-definite Hessian on
all of `E`. -/
theorem quadraticAffineObjective_hasPositiveDefiniteHessianOn
    (α : ℝ) (a : E) (A : E →L[ℝ] E)
    (hApos : ∀ u : E, u ≠ 0 → 0 < inner ℝ u (A u)) :
    HasPositiveDefiniteHessianOn (Set.univ : Set E) (quadraticAffineObjective α a A) := by
  let S : E →L[ℝ] E := selfAdjointPart ℝ A
  have hS : IsSelfAdjoint S := by
    simpa [S] using (selfAdjointPart ℝ A).2
  have hobj : quadraticAffineObjective α a A = quadraticAffineObjective α a S := by
    simpa [S] using quadraticAffineObjective_selfAdjointPart_eq α a A
  have hHess (x : E) : hessian (quadraticAffineObjective α a A) x = S := by
    rw [hobj]
    exact quadraticAffineObjective_hessian_eq α a S hS x
  refine ⟨?_, ?_⟩
  · intro x _
    have hSpos : S.IsPositive := by
      rw [ContinuousLinearMap.isPositive_iff']
      refine ⟨hS, ?_⟩
      intro u
      by_cases hu : u = 0
      · simp [hu]
      · rw [selfAdjointPart_apply_inner_eq]
        exact le_of_lt (by simpa [real_inner_comm] using hApos u hu)
    exact hHess x ▸ hSpos
  · intro x _ u hu
    rw [hHess x, inner_selfAdjointPart_apply_eq]
    exact hApos u hu

-- Proof sketch: if the quadratic objective were a `ν`-self-concordant barrier on all of `E`,
-- then the barrier-parameter inequality would hold for every base point and every direction.
-- Passing first to the self-adjoint part `S := selfAdjointPart ℝ A` does not change the quadratic
-- objective, and `quadraticAffineObjective_hasPositiveDefiniteHessianOn` upgrades the strict
-- positivity of `u ↦ ⟪u, A u⟫` to the Chapter 5 positive-definite-Hessian owner. Along the ray
-- `x = t • u` with `u ≠ 0`, the left-hand side then becomes a quadratic polynomial in `t` with
-- positive leading coefficient `2 * ⟪S u, u⟫ = 2 * ⟪A u, u⟫`, so it is unbounded above as
-- `t → ∞`, contradicting the uniform bound by `ν`.
/-- Example 5.3.1.2: if the quadratic form `u ↦ ⟪u, A u⟫` is strictly positive on nonzero
directions, then the quadratic function `x ↦ α + ⟪a, x⟫ + (1 / 2) ⟪A x, x⟫` on all of `E` is not
a `ν`-self-concordant barrier. -/
theorem quadraticAffineObjective_not_isSelfConcordantBarrierOnWith
    [Nontrivial E]
    (α : ℝ) (a : E) (A : E →L[ℝ] E) (ν : NNReal)
    (hApos : ∀ u : E, u ≠ 0 → 0 < inner ℝ u (A u)) :
    ¬ IsSelfConcordantBarrierOnWith (Set.univ : Set E) ν
      (quadraticAffineObjective α a A) := sorry

end

/-! ### Example_5_3_1_3 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

/- Example 5.3.1.3 lies in the scalar self-concordant-barrier domain.

Sampled owner-style declarations in this domain:
* `negLog_isStandardSelfConcordantOn` in `Example_5_1_3`, the chapter owner for the standard
  self-concordance of `x ↦ -log x` on `(0, ∞)`;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `gradient_eq_deriv'` in mathlib, the one-dimensional bridge from the Euclidean gradient to the
  usual scalar derivative;
* `deriv_log` in mathlib, the canonical logarithmic derivative formula used only at proof level.

Source/core/bridge triage:
* source-facing: the logarithmic barrier for the nonnegative ray, expressed on its open domain
  `(0, ∞)`;
* core/canonical: `IsSelfConcordantBarrierOnWith (Set.Ioi (0 : ℝ)) 1`;
* bridge/view: `negLog_isStandardSelfConcordantOn`, which supplies the standard
  self-concordance part of the barrier owner.

Primitive data:
* the scalar logarithmic barrier `x ↦ -log x`;
* the open barrier domain `(0, ∞)`;
* the barrier parameter `ν = 1`.

Derived API:
* standard self-concordance on `(0, ∞)`, reused from `negLog_isStandardSelfConcordantOn`;
* the scalar identities `F'(x) = -1 / x` and `F''(x) = 1 / x^2`, used only to discharge the
  barrier-parameter inequality.

This refinement therefore keeps the source-facing barrier theorem, but removes the impression that
the file owns a second self-concordance proof for `-log`. The core owner is the barrier class,
and the standard-self-concordance input is reused directly from the upstream chapter theorem. -/

-- Proof sketch: reuse `negLog_isStandardSelfConcordantOn` for the self-concordance part of the
-- owner. For the barrier inequality, use the scalar derivative formulas
-- `F'(x) = -1 / x` and `F''(x) = 1 / x^2`; then the one-dimensional identity
-- `(F'(x))^2 / F''(x) = 1` shows that the sharp barrier parameter is `ν = 1`.
/-- Example 5.3.1.3: the logarithmic barrier `x ↦ -log x`, defined on `(0, ∞)`, is a
`1`-self-concordant barrier for the nonnegative ray `{x : ℝ | 0 ≤ x}`. -/
theorem negLog_isSelfConcordantBarrierOnWith_nonnegativeRay :
    IsSelfConcordantBarrierOnWith (Set.Ioi (0 : ℝ)) 1 (fun x : ℝ ↦ -Real.log x) := by
  let f : ℝ → ℝ := quadraticAffineObjective 0 (-1 : ℝ) (0 : ℝ →L[ℝ] ℝ)
  have hf : f = fun x : ℝ ↦ -x := by
    funext x
    have hinner : inner ℝ (-1 : ℝ) x = -x := by
      convert (RCLike.inner_apply (-1 : ℝ) x) using 1
      simp
    rw [show f x = quadraticAffineObjective 0 (-1 : ℝ) (0 : ℝ →L[ℝ] ℝ) x by rfl]
    rw [quadraticAffineObjective_apply, ContinuousLinearMap.zero_apply]
    simp [hinner]
  have hdom : {x : ℝ | f x < 0} = Set.Ioi (0 : ℝ) := by
    ext x
    rw [Set.mem_setOf_eq, Set.mem_Ioi]
    rw [hf]
    constructor <;> intro hx <;> linarith
  have hbarrier_eq : sublevelLogBarrier f 0 = fun x : ℝ ↦ -Real.log x := by
    funext x
    rw [sublevelLogBarrier_apply, hf]
    congr 1
    simp
  have hstd :
      IsStandardSelfConcordantOn {x : ℝ | f x < 0} (sublevelLogBarrier f 0) := by
    simpa [hdom, hbarrier_eq] using negLog_isStandardSelfConcordantOn
  have hf_self : IsSelfConcordantOnWith (Set.univ : Set ℝ) 0 f := by
    simpa [f] using
      quadraticAffineObjective_isSelfConcordantOnWith_zero 0 (-1 : ℝ)
        (0 : ℝ →L[ℝ] ℝ) ContinuousLinearMap.isPositive_zero
  have hbarrier :
      IsSelfConcordantBarrierOnWith {x : ℝ | f x < 0} 1 (sublevelLogBarrier f 0) := by
    refine
      { toIsStandardSelfConcordantOn := hstd
        barrier_parameter_bound := ?_ }
    intro x hx u
    have hF_pos : (hessian (sublevelLogBarrier f 0) x).IsPositive :=
      hstd.hessian_isPositive hx
    have hbarrier_one :
        ∀ v : ℝ,
          2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
              inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ) := by
      have hiff :
          (∀ v : ℝ,
            2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ)) ↔
            ∀ v : ℝ,
              (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
        simpa using
          (show
            (∀ v : ℝ,
              2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                  inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ ((1 : NNReal) : ℝ)) ↔
              ∀ v : ℝ,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  ((1 : NNReal) : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) from
            barrier_parameter_bound_iff_gradient_inner_sq_le hF_pos)
      refine hiff.2 ?_
      intro v
      calc
        (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
            ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
          simpa using hf_self.sublevelLogBarrier_gradient_inner_sq_le 0 (by simp) hx
        _ = (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
          ring
    exact hbarrier_one u
  simpa [hdom, hbarrier_eq] using hbarrier

/-! ### Example_5_3_1_4 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Example 5.3.1.4 lies in the Chapter 5 self-concordant-barrier / logarithmic-sublevel-barrier
domain.

Sampled owner-style declarations in this domain:
* `quadraticAffineObjective` in `Example_5_1_2`, the chapter source-facing owner for affine-
  quadratic objectives;
* `logAffineQuadraticBarrier_isStandardSelfConcordantOn` in `Example_5_1_4`, the canonical
  standard-self-concordance theorem for this exact logarithmic barrier;
* `IsSelfConcordantOnWith.sublevelLogBarrier_gradient_inner_sq_le` in `Theorem_5_1_4`, the
  canonical owner-level squared barrier inequality for logarithmic sublevel barriers;
* `barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the canonical bridge
  from that squared inequality to the barrier-parameter owner;
* `selfAdjointPart`, together with the bridge lemmas from `Example_5_3_1_2`, the canonical
  projection showing that this barrier depends only on the symmetric quadratic form.

Source/core/bridge triage:
* source-facing: the logarithmic barrier of the concave affine-quadratic potential
  `φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`;
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* bridge/view: the canonical strict sublevel barrier
  `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0`.

Primitive data:
* `α`, `a`, and `A`;
* nonnegativity of the quadratic form `u ↦ ⟪u, A u⟫`.

Derived API:
* the self-adjoint part `selfAdjointPart ℝ A`, which preserves the quadratic term and carries the
  positivity owner needed upstream;
* standard self-concordance of the logarithmic barrier, reused from `Example_5_1_4`;
* the barrier inequality with parameter `1`, derived from the canonical owner-level sublevel-
  barrier estimate and `Proposition_5.3.3`.

This refinement keeps the theorem source-facing, but deletes the duplicate-wheel direct
differentiation route in favor of the upstream Chapter 5 owners already attached to the same
barrier. -/

-- Proof sketch: rewrite the source-facing barrier as the canonical strict sublevel barrier
-- `sublevelLogBarrier (quadraticAffineObjective (-α) (-a) A) 0`. Theorem `5.1.4` gives the
-- squared gradient-versus-local-norm estimate for this sublevel barrier, Proposition `5.3.3`
-- converts that estimate into the barrier-parameter inequality with `ν = 1`, and
-- `Example_5_1_4` already supplies the standard-self-concordance part of the barrier owner.
/-- Example 5.3.1.4: if the quadratic form `u ↦ ⟪u, A u⟫` is nonnegative, then the logarithmic
barrier associated to the concave affine-quadratic potential
`φ(x) = α + ⟪a, x⟫ - (1 / 2) ⟪A x, x⟫`
is a `1`-self-concordant barrier on its positivity domain `{x | φ(x) > 0}`. -/
theorem negLog_concaveQuadratic_isSelfConcordantBarrierOnWith
    (α : ℝ) (a : E) (A : E →L[ℝ] E)
    (hA_posSemidef : ∀ u : E, 0 ≤ inner ℝ u (A u)) :
    IsSelfConcordantBarrierOnWith
      {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x}
      1
      (fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x)) := by
  let S : E →L[ℝ] E := selfAdjointPart ℝ A
  let f : E → ℝ := quadraticAffineObjective (-α) (-a) S
  have hS_selfAdjoint : IsSelfAdjoint S := by
    simpa [S] using (selfAdjointPart ℝ A).2
  have hS_pos : S.IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff']
    refine ⟨hS_selfAdjoint, ?_⟩
    intro u
    calc
      0 ≤ inner ℝ u (A u) := hA_posSemidef u
      _ = inner ℝ (S u) u := by
            rw [real_inner_comm]
            simpa [S] using (selfAdjointPart_apply_inner_eq A u).symm
  have hstd :
      IsStandardSelfConcordantOn
        {x : E | f x < 0}
        (sublevelLogBarrier f 0) := by
    convert logAffineQuadraticBarrier_isStandardSelfConcordantOn α a S hS_pos using 1
    · simpa [f] using quadraticAffineObjective_neg_strictSublevel_eq α a S
    · simpa [f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq α a S
  have hf_self : IsSelfConcordantOnWith (Set.univ : Set E) 0 f := by
    simpa [f] using quadraticAffineObjective_isSelfConcordantOnWith_zero (-α) (-a) S hS_pos
  have hbarrier :
      IsSelfConcordantBarrierOnWith
        {x : E | f x < 0}
        1
        (sublevelLogBarrier f 0) := by
    refine
      { toIsStandardSelfConcordantOn := hstd
        barrier_parameter_bound := ?_ }
    intro x hx u
    have hbarrier_one :
        ∀ v : E,
          2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
              inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ) := by
      have hiff :
          (∀ v : E,
            2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤ (1 : ℝ)) ↔
              ∀ v : E,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  (1 : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) := by
        simpa using
          (show
            (∀ v : E,
              2 * inner ℝ (∇ (sublevelLogBarrier f 0) x) v -
                  inner ℝ v (hessian (sublevelLogBarrier f 0) x v) ≤
                    ((1 : NNReal) : ℝ)) ↔
              ∀ v : E,
                (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
                  ((1 : NNReal) : ℝ) * ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ) from
            barrier_parameter_bound_iff_gradient_inner_sq_le
              (hstd.hessian_isPositive hx))
      refine hiff.2 ?_
      intro v
      simpa using
        (hf_self.sublevelLogBarrier_gradient_inner_sq_le 0 (by simp) hx :
          (inner ℝ (∇ (sublevelLogBarrier f 0) x) v) ^ (2 : ℕ) ≤
            ‖v‖[sublevelLogBarrier f 0; x] ^ (2 : ℕ))
    exact hbarrier_one u
  have hdom :
      {x : E | f x < 0} =
        {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
    calc
      {x : E | f x < 0}
          = {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (S x) x} := by
              simpa [f] using quadraticAffineObjective_neg_strictSublevel_eq α a S
      _ = {x : E | 0 < α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x} := by
            ext x
            have hquad : inner ℝ (S x) x = inner ℝ (A x) x := by
              simpa [S] using selfAdjointPart_apply_inner_eq A x
            simp [hquad]
  have hfun :
      sublevelLogBarrier f 0 =
        fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
    calc
      sublevelLogBarrier f 0
          = fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (S x) x) := by
              simpa [f] using sublevelLogBarrier_quadraticAffineObjective_neg_eq α a S
      _ = fun x ↦ -Real.log (α + inner ℝ a x - (1 / 2 : ℝ) * inner ℝ (A x) x) := by
            funext x
            have hquad : inner ℝ (S x) x = inner ℝ (A x) x := by
              simpa [S] using selfAdjointPart_apply_inner_eq A x
            simp [hquad]
  simpa [hdom, hfun] using hbarrier

end

/-! ### Lemma_5_3_1 (from Chap05) -/
noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The ambient exponential transform attached to a barrier candidate `F` and positive parameter
`p`. -/
def barrierExponentialTransform (p : NNRealˣ) (F : E → ℝ) : E → ℝ :=
  fun x ↦ Real.exp (-F x / (p : ℝ))

/- Lemma 5.3.1 lies in the Chapter 5 self-concordant-barrier / exponential-transform domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantOnWith` and `IsStandardSelfConcordantOn` in `Definition_5_1_1`, the chapter
  owners for self-concordance on an open convex domain;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the chapter owner for a
  `ν`-self-concordant barrier;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the
  canonical pointwise reformulation of the barrier inequality;
* `isSelfConcordantBarrierOnWith_iff_logarithmic_taylor_lower_bound` in `Theorem_5_3_7`, the
  later source-facing barrier characterization obtained from the same owner.

Best owner abstraction:
* core/canonical: `IsSelfConcordantBarrierOnWith`;
* source-facing: the numbered equivalence between the barrier owner and concavity of the
  exponential transform when the underlying function is already standard self-concordant;
* bridge/view: the ambient exponential-transform owner
  `barrierExponentialTransform p F` together with the owner-level concavity theorem for barrier
  parameters `p ≥ ν`.

Primitive data:
* a domain `dom`;
* a function `F`;
* a barrier parameter `p`;
* the ambient exponential transform `barrierExponentialTransform p F` for `p : NNRealˣ`;
* either the barrier owner `IsSelfConcordantBarrierOnWith dom ν F` or the standard
  self-concordance owner `IsStandardSelfConcordantOn dom F` together with the displayed concavity
  condition.

Derived API:
* concavity of `barrierExponentialTransform p F` for every positive `p ≥ ν`;
* the source-facing equivalence at `p = ν`.

Source/core/bridge triage:
* source-facing: the equivalence in Lemma 5.3.1;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`;
* bridge/view: owner-level concavity of the exponential transform.

This refinement therefore places the auxiliary concavity statement in the barrier owner namespace
and leaves the numbered equivalence as the public source-facing theorem. -/

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: compute the Hessian quadratic form of `x ↦ exp (-(F x / p))`; the displayed
-- formula in the text shows that concavity follows from the barrier inequality with parameter
-- `ν`, and if `p ≥ ν` then the same estimate remains valid with `p` in place of `ν`.
/-- If `F` is a `ν`-self-concordant barrier on `dom`, then every exponential transform
`x ↦ exp (-(F x / p))` with positive `p ≥ ν` is concave on `dom`. This is the owner-level concavity
companion to Lemma `5.3.1`. -/
theorem concaveOn_exp_neg_div
    {dom : Set E} {ν : NNReal} {p : NNRealˣ} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F) (hνp : ν ≤ (p : NNReal)) :
    ConcaveOn ℝ dom (barrierExponentialTransform p F) := sorry

end IsSelfConcordantBarrierOnWith

-- Proof sketch: for the forward implication, specialize the Hessian computation of
-- `x ↦ exp (-(F x / ν))` and rewrite the concavity condition as the barrier inequality from
-- Definition 5.3.2. For the reverse implication, the same computation turns concavity of
-- `x ↦ exp (-(F x / ν))` into the barrier-parameter bound, while the standard self-concordance
-- assumption supplies the remaining part of the barrier structure. The positivity hypothesis on
-- `ν` is essential, because the owner-level transform in the auxiliary API is only defined for a
-- positive parameter, but the numbered equivalence is stated directly with the textbook function
-- `x ↦ exp (-(F x / ν))`.
/-- Lemma 5.3.1: for a standard self-concordant function `F` on `dom` and a positive barrier
parameter `ν`, being a `ν`-self-concordant barrier is equivalent to concavity of the exponential
transform `x ↦ exp (-(F x / ν))` on `dom`. -/
theorem isSelfConcordantBarrierOnWith_iff_concaveOn_exp_neg_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hFsc : IsStandardSelfConcordantOn dom F) (hν : 0 < (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith dom ν F ↔
      ConcaveOn ℝ dom (fun x ↦ Real.exp (-(F x / (ν : ℝ)))) := sorry

end

/-! ### Proposition_5_3_1 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

/-
Proposition 5.3.1 lies in the chapter's central-path / first-order stationarity domain.

Sampled owner-style declarations:
- `centralPathPenaltyObjective` in `Definition_5_3_6_1`, the Chapter 5 owner for the tilted
  objective `x ↦ t ⟪c, x⟫ + f x`;
- `IsCentralPath` in `Definition_5_3_6_1`, the owner predicate asserting pointwise minimizers of
  that objective;
- `IsMinOn.isLocalMin`, the canonical bridge from a feasible-set minimizer to an ambient local
  minimizer once the feasible set is a neighborhood of the minimizer;
- `isLocalMin_gradient_eq_zero` in `Chap01/Theorem_1_4_13`, the source-facing stationarity theorem
  for local minimizers on complete real inner-product spaces.

Best owner abstraction:
- source-facing: the central-path stationarity equation in the penalty objective;
- core/canonical: `centralPathPenaltyObjective`, `IsCentralPath`, and `HasGradientAt`;
- bridge/view: the pointwise gradient computation for the penalty objective and the deduction of
  the displayed zero-gradient equation from the owner local-minimum theorem.

Primitive data:
- a domain `dom : Set E`;
- an objective vector `c : E`;
- a differentiable function `f : E → ℝ`;
- a trajectory `xStar : Set.Ici (0 : ℝ) → dom`.

Derived API:
- the gradient identity for `centralPathPenaltyObjective c f t`;
- the stationarity equation satisfied by a central-path point.

This file is therefore a `bridge/view` layer over the existing Chapter 5 central-path owner and
the Chapter 1 stationary-point owner. No parallel local central-path wrapper is introduced. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: differentiate the linear term `x ↦ (t : ℝ) * ⟪c, x⟫`, whose gradient is
-- `t • c`, then add the canonical gradient of `f`.
/-- The tilted objective `x ↦ t ⟪c, x⟫ + f(x)` has gradient `(t : ℝ) • c + ∇ f x` at every
point where `f` is differentiable. -/
theorem hasGradientAt_centralPathPenaltyObjective
    (c : E) (f : E → ℝ) (t : ℝ) {x : E}
    (hf : DifferentiableAt ℝ f x) :
    HasGradientAt (centralPathPenaltyObjective c f t) (t • c + ∇ f x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hlinear : HasFDerivAt (fun z : E ↦ t * inner ℝ c z) ((t : ℝ) • innerSL ℝ c) x := by
    simpa using (((t : ℝ) • innerSL ℝ c).hasFDerivAt :
      HasFDerivAt (fun z : E ↦ ((t : ℝ) • innerSL ℝ c) z) ((t : ℝ) • innerSL ℝ c) x)
  simpa [centralPathPenaltyObjective] using hlinear.add hf.hasGradientAt.hasFDerivAt

-- Proof sketch: for a fixed `t`, the central-path point `x*(t)` is a global minimizer of the
-- tilted objective on `dom`. If `dom` is a neighborhood of `x*(t)`, then this is an ambient
-- local minimizer. Apply Fermat's theorem to `x ↦ (t : ℝ) * ⟪c, x⟫ + f(x)` and then rewrite the
-- gradient using `hasGradientAt_centralPathPenaltyObjective`.
/-- Proposition 5.3.1: if `x*(t)` minimizes the tilted objective
`x ↦ t ⟪c, x⟫ + f(x)` for every `t ≥ 0`, then at each parameter `t` where `dom` is a
neighborhood of `x*(t)` and `f` is differentiable at `x*(t)`, it satisfies the central-path
stationarity equation `(t : ℝ) • c + ∇ f(x*(t)) = 0`. -/
theorem centralPath_stationarity_eq_zero
    (dom : Set E) (c : E) (f : E → ℝ) (xStar : Set.Ici (0 : ℝ) → dom)
    (hpath : IsCentralPath dom c f xStar)
    (t : Set.Ici (0 : ℝ))
    (hdom : dom ∈ nhds (xStar t : E))
    (hf : DifferentiableAt ℝ f (xStar t : E)) :
    (t : ℝ) • c + ∇ f (xStar t : E) = 0 := by
  have hmin : IsMinOn (centralPathPenaltyObjective c f t) dom (xStar t : E) := hpath t
  have hlocal : IsLocalMin (centralPathPenaltyObjective c f t) (xStar t : E) :=
    hmin.isLocalMin hdom
  have hgrad :
      ∇ (centralPathPenaltyObjective c f (t : ℝ)) (xStar t : E) =
        (t : ℝ) • c + ∇ f (xStar t : E) :=
    (hasGradientAt_centralPathPenaltyObjective c f (t : ℝ) hf).gradient
  have hgradzero : ∇ (centralPathPenaltyObjective c f t) (xStar t : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  rw [hgrad] at hgradzero
  exact hgradzero

end

/-! ### Theorem_5_3_1 (from Chap05) -/
noncomputable section

universe u

/- Theorem 5.3.1 lies in the chapter's self-concordance / affine-perturbation domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantOnWith` and `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter
  owners for self-concordance;
* `quadraticAffineObjective` and `quadraticAffineObjective_zero_operator` from `Example_5_1_2`,
  the source-facing affine-quadratic owner and its zero-quadratic bridge to a linear term;
* `IsSelfConcordantOnWith.add_quadraticAffineObjective` from `Corollary_5_1_2`, the owner-level
  perturbation theorem for preserving self-concordance.

Source/core/bridge triage:
* source-facing: the linear perturbation `x ↦ ⟪c, x⟫ + F x`;
* core/canonical: `IsStandardSelfConcordantOn dom F`;
* bridge/view: `quadraticAffineObjective_zero_operator`, identifying the linear term with the
  zero-quadratic specialization of `quadraticAffineObjective`.

Primitive data:
* the domain `dom`;
* the standard self-concordant objective `F`;
* the perturbation vector `c`.

Derived API:
* positivity of the zero operator;
* the zero-operator bridge
  `quadraticAffineObjective 0 c (0 : E →L[ℝ] E) = fun x ↦ inner ℝ c x`;
* the specialization of `IsSelfConcordantOnWith.add_quadraticAffineObjective` to
  `quadraticAffineObjective 0 c 0`.

The target statement is therefore kept source-facing, while its implementation is refined to the
chapter owner theorem and the owner zero-operator bridge instead of a parallel local proof
route. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply Corollary 5.1.2 to the standard self-concordant function `F` with
-- quadratic-affine perturbation data `α = 0`, `a = c`, and `A = 0`. The zero operator is
-- positive semidefinite, and `quadraticAffineObjective_zero_operator` identifies this
-- specialization with the linear term `x ↦ inner ℝ c x`.
/-- Theorem 5.3.1: if `F` is standard self-concordant on `dom`, then the linear perturbation
`x ↦ ⟪c, x⟫ + F(x)` is standard self-concordant on `dom`. This is the self-concordance part of
the textbook statement for a self-concordant barrier. -/
theorem selfConcordantBarrier_add_linear_isStandardSelfConcordantOn
    (dom : Set E) (F : E → ℝ) (c : E) (hF : IsStandardSelfConcordantOn dom F) :
    IsStandardSelfConcordantOn dom (fun x ↦ inner ℝ c x + F x) := by
  simpa [quadraticAffineObjective_zero_operator, add_comm, add_left_comm, add_assoc] using
    hF.add_quadraticAffineObjective 0 c (0 : E →L[ℝ] E) ContinuousLinearMap.isPositive_zero

end

/-! ### Corollary_5_3_2 (from Chap05) -/
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Corollary 5.3.2 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the barrier owner;
* `IsSelfConcordantOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` from
  `Theorem_5_1_14`, the canonical self-concordant recession-direction estimate used here;
* `hessianLocalNorm` and `‖u‖[F; x]` from `Definition_5_1_1`, the canonical local-norm owner.

Source/core/bridge triage:
* source-facing: the barrier specialization of the recession-direction estimate;
* core/canonical: `IsSelfConcordantBarrierOnWith dom ν F`, viewed through its parent
  `IsSelfConcordantOnWith dom 1 F`;
* bridge/view: the barrier-specific derivation of the nonascent and backward-frontier hypotheses
  needed to apply Theorem 5.1.14.

This corollary is a barrier-owner specialization of the Chapter 5 recession-direction estimate, so
its public surface should live on `IsSelfConcordantBarrierOnWith` rather than as a parallel
top-level theorem repeating the owner theorem's name. -/

namespace IsSelfConcordantBarrierOnWith

section

variable {dom : Set E} {ν : NNReal} {F : E → ℝ}
variable {h x : E}

-- Proof sketch: use inequality `(5.3.10)` to show that every recession direction is a
-- nonascent direction for a self-concordant barrier. If the backward ray from `x` in direction
-- `h` hits `frontier dom` at finite distance, apply the owner theorem
-- `IsSelfConcordantOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` to the
-- inherited standard self-concordant structure with parameter `1`; if `dom` contains the whole
-- line `x + ℝ • h`, then `F` is constant along that line and both sides vanish.
/-- Corollary 5.3.2: if `F` is a `ν`-self-concordant barrier on `dom` and `h` is a recession
direction of `dom`, then at every `x ∈ dom` the Hessian local norm of `h` is bounded by the
pairing of `h` with the negative gradient. -/
theorem hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hrecession : ∀ ⦃y : E⦄, y ∈ dom → ∀ τ : ℝ, 0 ≤ τ → y + τ • h ∈ dom)
    (hx : x ∈ dom)
    :
    ‖h‖[F; x] ≤ inner ℝ (-∇ F x) h := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  let hself : IsSelfConcordantOnWith dom 1 F := inferInstance
  sorry

-- Proof sketch: combine the owner-level local-norm bound above with the nonnegativity of the
-- Hessian local norm. This turns the recession-direction estimate into a direct nonpositivity
-- statement for the gradient pairing itself.
/-- For a self-concordant barrier, the gradient pairing with any recession direction of the
domain is nonpositive. -/
theorem inner_gradient_nonpos_of_recession_direction
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    (hrecession : ∀ ⦃y : E⦄, y ∈ dom → ∀ τ : ℝ, 0 ≤ τ → y + τ • h ∈ dom)
    (hx : x ∈ dom)
    :
    inner ℝ (∇ F x) h ≤ 0 := by
  have hbound :=
    hF.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction hrecession hx
  have hneg : 0 ≤ inner ℝ (-∇ F x) h :=
    le_trans (hessianLocalNorm_nonneg F x h) hbound
  exact neg_nonneg.mp <| by simpa [inner_neg_left] using hneg

end

end IsSelfConcordantBarrierOnWith

end

/-! ### Definition_5_3_2 (from Chap05) -/
open Set Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.3.2 lies in the Chapter 5 self-concordant-barrier domain.

Sampled owner-style declarations in this domain:
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for standard
  self-concordance on an open convex domain;
* `IsBarrierFunctionOn` from `Chap01/Definition_1_10_18`, the canonical closed-domain barrier
  owner expressed through a bundled map on `interior (closure dom)`;
* `IsSelfConcordantOnWith.toBarrierMap` and `IsSelfConcordantOnWith.isBarrierFunctionOn` from
  `Theorem_5_1_3`, the canonical bridge turning self-concordance on `dom` into the Chapter 1
  barrier owner on `closure dom`.

Best owner abstraction:
* source-facing: `IsSelfConcordantBarrierOnWith dom ν F`;
* core/canonical ambient owners: `IsStandardSelfConcordantOn dom F` and
  `IsBarrierFunctionOn (closure dom) ...`;
* bridge/view: the finite-dimensional theorem
  `IsSelfConcordantBarrierOnWith.isBarrierFunctionOn`.

Primitive data:
* the standard self-concordance owner on `dom`;
* the pointwise barrier-parameter inequality.

Derived API:
* standard self-concordance as an inferable parent instance;
* the barrier-parameter inequality as a theorem-level owner consequence;
* the finite-dimensional bridge to `IsBarrierFunctionOn (closure dom)`.

Source/core/bridge triage:
* source-facing: `IsSelfConcordantBarrierOnWith dom ν F`;
* core/canonical: `IsStandardSelfConcordantOn dom F` and `IsBarrierFunctionOn`;
* bridge/view: `isBarrierFunctionOn`.

This file therefore keeps the source-facing barrier owner, but removes unused `Fact` wrappers
around derived consequences. The owner-level consequences are exposed directly as theorems instead
of parallel typeclass packaging. -/

/-- Definition 5.3.2: a standard self-concordant function `F` is a `ν`-self-concordant barrier
for `dom` when, for every `x ∈ dom`, every direction `u` satisfies the barrier inequality
`2 ⟪∇F(x), u⟫ - ⟪u, ∇²F(x)u⟫ ≤ ν`. The constant `ν` is the barrier parameter. The Chapter 1
barrier owner on `closure dom` is a separate finite-dimensional bridge that additionally needs
domain nonemptiness. -/
class IsSelfConcordantBarrierOnWith (dom : Set E) (ν : NNReal) (F : E → ℝ) : Prop where
  /-- A self-concordant barrier is standard self-concordant on its open convex domain. -/
  toIsStandardSelfConcordantOn : IsStandardSelfConcordantOn dom F
  /-- The barrier parameter bounds the gradient term by the Hessian quadratic form at each point
  of the domain. -/
  barrier_parameter_bound {x : E} (hx : x ∈ dom) (u : E) :
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)

attribute [instance] IsSelfConcordantBarrierOnWith.toIsStandardSelfConcordantOn

namespace IsSelfConcordantBarrierOnWith

/-- A self-concordant barrier instance canonically supplies the defining barrier-parameter
inequality at each point of its domain. -/
theorem barrier_parameter_bound_of_mem
    {dom : Set E} (ν : NNReal) {F : E → ℝ}
    [h : IsSelfConcordantBarrierOnWith dom ν F] {x : E} (hx : x ∈ dom) (u : E) :
    2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ) :=
  h.barrier_parameter_bound hx u

variable [FiniteDimensional ℝ E]

/-- A self-concordant barrier canonically supplies the Chapter 1 barrier owner on `closure dom`
through the restricted map `interior (closure dom) = dom → ℝ`. -/
theorem isBarrierFunctionOn
    {dom : Set E} {ν : NNReal} {F : E → ℝ} (h : IsSelfConcordantBarrierOnWith dom ν F)
    (hdom : dom.Nonempty) :
    IsBarrierFunctionOn (closure dom) h.toIsStandardSelfConcordantOn.toBarrierMap :=
  h.toIsStandardSelfConcordantOn.isBarrierFunctionOn hdom

end IsSelfConcordantBarrierOnWith

end

/-! ### Lemma_5_3_2 (from Chap05) -/
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: rewrite the approximate-centering hypothesis as
-- `t ‖c‖*_x ≤ ‖t c + ∇ F(x)‖*_x + ‖∇ F(x)‖*_x` by the triangle inequality for the dual local norm.
-- Then use the barrier gradient estimate `‖∇ F(x)‖*_x ≤ √ν`, which is the inverse-Hessian form of
-- the barrier-parameter bound, and divide by the positive scalar `t`.
/-- Lemma 5.3.2: if `x` in the domain of a `ν`-self-concordant barrier `F` satisfies the
approximate-centering condition `‖t c + ∇ F(x)‖*ₓ ≤ β` for some `t > 0`, then the dual local norm
of the objective vector is bounded by `‖c‖*ₓ ≤ (β + √ν) / t`. -/
theorem dualLocalNorm_objectiveVector_le_add_sqrt_barrierParameter_div
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    [IsSelfConcordantBarrierOnWith dom ν F]
    (c : E) {t β : ℝ} (ht : 0 < t)
    {x : dom}
    (hH : (fderiv ℝ (∇ F) (x : E)).det ≠ 0)
    (happrox :
      HessianDualLocalNorm.ofDetNeZero F (x : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
        ((InnerProductSpace.toDual ℝ E) (t • c + ∇ F (x : E))) ≤ β) :
    HessianDualLocalNorm.ofDetNeZero F (x : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 x.2) hH
      ((InnerProductSpace.toDual ℝ E) c) ≤
      (β + Real.sqrt (ν : ℝ)) / t := sorry

end

/-! ### Proposition_5_3_2 (from Chap05) -/
open scoped Gradient NewtonDecrement

noncomputable section

universe u

/- This file lies in the Chapter 5 barrier-parameter / Newton-decrement domain.

Sampled owner declarations in this domain:
* `newtonDecrement` and `newtonDecrement_def` in `Definition_5_0_24`, the pointwise owner for the
  Newton decrement from local Hessian positivity and invertibility data;
* `NewtonDecrement.ofPosDefMem` and `NewtonDecrement.ofPosDefMem_def` in `Definition_5_0_24`, the
  positive-definite-Hessian domain bridge obtained from `x ∈ dom`;
* `HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem` and
  `HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem` in `Definition_5_0_23`, the canonical
  way to derive the local Hessian data from domain hypotheses;
* `barrier_parameter_bound_iff_gradient_inner_sq_le` in `Proposition_5_3_3`, the local-norm-square
  companion reformulation of the same fixed-point inequality.

Best owner abstraction:
* source-facing: the fixed-point barrier inequality in all directions;
* core/canonical: the Chapter 5 Newton decrement owners `λ[F; x | hPos; hInv]` and `λ[F; x | hx]`;
* bridge/view: `newtonDecrement_def` and `NewtonDecrement.ofPosDefMem_def`, which rewrite those
  owner surfaces as the inverse-Hessian gradient pairing.

Primitive data:
* a function `F`, a point `x`, and a barrier parameter `ν`;
* the pointwise Hessian positivity and invertibility data at `x`.

Derived API:
* the pointwise Newton-decrement bound `λ[F; x | hPos; hInv] ≤ √ν`;
* the inverse-Hessian gradient pairing bound as a companion reformulation;
* the domain-level Newton-decrement bound `λ[F; x | hx] ≤ √ν`.

The public surface therefore states Proposition 5.3.2 first on the Chapter 5 pointwise owner
`λ[F; x | hPos; hInv]`, keeps the inverse-Hessian pairing only as a companion reformulation for
duality arguments, and reserves `λ[F; x | hx]` for the separate positive-definite-domain bridge. -/

section PointwiseOwner

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: complete the square with
-- `u - (hessian F x).inverse (∇ F x)` and then rewrite the maximizing value by
-- `newtonDecrement_def`, identifying it with the pointwise Newton decrement
-- `λ[F; x | hPos; hInv]`.
/-- Proposition 5.3.2, pointwise owner form: if the Hessian at `x` is positive and invertible,
then the barrier inequality from Definition 5.3.2 is equivalent to the Chapter 5 pointwise
Newton-decrement bound `λ[F; x | hPos; hInv] ≤ √ν`. -/
theorem barrier_parameter_bound_iff_newtonDecrement_le_sqrt
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      λ[F; x | hPos; hInv] ≤ Real.sqrt (ν : ℝ) := sorry

end PointwiseOwner

section PointwiseCompanion

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: complete the square with
-- `u - (hessian F x).inverse (∇ F x)` and use the positive / invertible Hessian supplied by the
-- pointwise hypotheses at `x` to identify the supremum of
-- `2 ⟪∇ F(x), u⟫ - ⟪∇² F(x)u, u⟫` with the inverse-Hessian pairing
-- `⟪∇ F(x), (∇² F(x))⁻¹ ∇ F(x)⟫`.
/-- Proposition 5.3.2, companion inverse-Hessian form: if the Hessian at `x` is positive and
invertible, then the barrier inequality from Definition 5.3.2 is equivalent to the
inverse-Hessian pairing bound `⟪∇ F(x), [∇² F(x)]⁻¹ ∇ F(x)⟫ ≤ ν`. -/
theorem barrier_parameter_bound_iff_gradient_inverse_hessian_gradient_le
    {F : E → ℝ} {ν : NNReal} {x : E} (hPos : (hessian F x).IsPositive)
    (hInv : (hessian F x).IsInvertible) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      inner ℝ (∇ F x) ((hessian F x).inverse (∇ F x)) ≤ (ν : ℝ) := sorry

end PointwiseCompanion

section NewtonDecrementBridge

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the pointwise owner theorem
-- `barrier_parameter_bound_iff_newtonDecrement_le_sqrt` to the positive and invertible Hessian
-- witnesses canonically supplied by `HasPositiveDefiniteHessianOn dom F`, then identify the
-- resulting pointwise owner with the domain notation `λ[F; x | hx]`.
/-- Under the positive-definite-Hessian owner hypothesis, the domain-level bridge form of
the fixed-point barrier inequality is equivalently the owner-level Newton-decrement bound
`λ[F; x | hx] ≤ √ν`. -/
theorem barrier_parameter_bound_iff_newtonDecrement_ofPosDefMem_le_sqrt
    {dom : Set E} {F : E → ℝ} {ν : NNReal} [HasPositiveDefiniteHessianOn dom F] {x : E}
    (hx : x ∈ dom) :
    (∀ u : E,
      2 * inner ℝ (∇ F x) u - inner ℝ u (hessian F x u) ≤ (ν : ℝ)) ↔
      λ[F; x | hx] ≤ Real.sqrt (ν : ℝ) := sorry

end NewtonDecrementBridge

end

/-! ### Theorem_5_3_2 (from Chap05) -/
open Set Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace IsSelfConcordantBarrierOnWith

-- Proof sketch: the standard self-concordance component is the owner theorem
-- `IsStandardSelfConcordantOn.add`. For the barrier parameter, expand the gradient and Hessian of
-- the sum at `x ∈ dom₁ ∩ dom₂`; the displayed expression splits into the two summand barrier
-- expressions, which are bounded by `ν₁` and `ν₂`.
/-- Theorem 5.3.2: the pointwise sum of a `ν₁`-self-concordant barrier `F₁` on `dom₁` and a
`ν₂`-self-concordant barrier `F₂` on `dom₂` is a `(\nu₁ + \nu₂)`-self-concordant barrier on the
intersection domain `dom₁ ∩ dom₂`. -/
theorem add
    {dom₁ dom₂ : Set E} {ν₁ ν₂ : NNReal} {F₁ F₂ : E → ℝ}
    (h₁ : IsSelfConcordantBarrierOnWith dom₁ ν₁ F₁)
    (h₂ : IsSelfConcordantBarrierOnWith dom₂ ν₂ F₂) :
    IsSelfConcordantBarrierOnWith (dom₁ ∩ dom₂) (ν₁ + ν₂) (F₁ + F₂) := by
  let hself₁ : IsStandardSelfConcordantOn dom₁ F₁ := h₁.toIsStandardSelfConcordantOn
  let hself₂ : IsStandardSelfConcordantOn dom₂ F₂ := h₂.toIsStandardSelfConcordantOn
  refine
    { toIsStandardSelfConcordantOn := by simpa using hself₁.add hself₂
      barrier_parameter_bound := ?_ }
  intro x hx u
  rcases hx with ⟨hx₁, hx₂⟩
  have hbound₁ := h₁.barrier_parameter_bound hx₁ u
  have hbound₂ := h₂.barrier_parameter_bound hx₂ u
  have hF₁ : DifferentiableAt ℝ F₁ x := by
    exact
      (hself₁.contDiffOn.contDiffAt (hself₁.isOpen_domain.mem_nhds hx₁)).differentiableAt
        (by norm_num)
  have hF₂ : DifferentiableAt ℝ F₂ x := by
    exact
      (hself₂.contDiffOn.contDiffAt (hself₂.isOpen_domain.mem_nhds hx₂)).differentiableAt
        (by norm_num)
  have hgrad : ∇ (F₁ + F₂) x = ∇ F₁ x + ∇ F₂ x := by
    rw [gradient, fderiv_add hF₁ hF₂]
    simp [gradient]
  have hF₁_c2 : ContDiffOn ℝ 2 F₁ dom₁ := hself₁.contDiffOn.of_le (by norm_num)
  have hF₂_c2 : ContDiffOn ℝ 2 F₂ dom₂ := hself₂.contDiffOn.of_le (by norm_num)
  have hfderiv₁ : DifferentiableAt ℝ (fderiv ℝ F₁) x := by
    exact
      ((hF₁_c2.fderiv_of_isOpen hself₁.isOpen_domain
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
        (by simp) x hx₁).differentiableAt (hself₁.isOpen_domain.mem_nhds hx₁)
  have hfderiv₂ : DifferentiableAt ℝ (fderiv ℝ F₂) x := by
    exact
      ((hF₂_c2.fderiv_of_isOpen hself₂.isOpen_domain
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn
        (by simp) x hx₂).differentiableAt (hself₂.isOpen_domain.mem_nhds hx₂)
  have hgradF₁ : DifferentiableAt ℝ (∇ F₁) x := by
    unfold gradient
    simpa using ((InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp x hfderiv₁)
  have hgradF₂ : DifferentiableAt ℝ (∇ F₂) x := by
    unfold gradient
    simpa using ((InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp x hfderiv₂)
  have hgrad_nhds : (fun y ↦ ∇ (F₁ + F₂) y) =ᶠ[𝓝 x] fun y ↦ ∇ F₁ y + ∇ F₂ y := by
    filter_upwards [hself₁.isOpen_domain.mem_nhds hx₁, hself₂.isOpen_domain.mem_nhds hx₂] with
      y hy₁ hy₂
    have hFy₁ : DifferentiableAt ℝ F₁ y := by
      exact
        (hself₁.contDiffOn.contDiffAt (hself₁.isOpen_domain.mem_nhds hy₁)).differentiableAt
          (by norm_num)
    have hFy₂ : DifferentiableAt ℝ F₂ y := by
      exact
        (hself₂.contDiffOn.contDiffAt (hself₂.isOpen_domain.mem_nhds hy₂)).differentiableAt
          (by norm_num)
    rw [gradient, fderiv_add hFy₁ hFy₂]
    simp [gradient]
  have hhess : hessian (F₁ + F₂) x = hessian F₁ x + hessian F₂ x := by
    rw [hessian, hgrad_nhds.fderiv_eq, fderiv_fun_add hgradF₁ hgradF₂]
  calc
    2 * inner ℝ (∇ (F₁ + F₂) x) u - inner ℝ u (hessian (F₁ + F₂) x u)
        = (2 * inner ℝ (∇ F₁ x) u - inner ℝ u (hessian F₁ x u)) +
            (2 * inner ℝ (∇ F₂ x) u - inner ℝ u (hessian F₂ x u)) := by
          rw [hgrad, hhess]
          simp [inner_add_left, inner_add_right, ContinuousLinearMap.add_apply, two_mul,
            sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ ≤ (ν₁ : ℝ) + (ν₂ : ℝ) := add_le_add hbound₁ hbound₂
    _ = ((ν₁ + ν₂ : NNReal) : ℝ) := by exact_mod_cast rfl

end IsSelfConcordantBarrierOnWith

end
