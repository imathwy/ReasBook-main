import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_13_3_1 (from Chap03) -/
section

open scoped Rockafellar

universe u v w

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable {E : Type u} {EStar : Type v}
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommMonoid EStar] [Module 𝕜 EStar]
variable [HasLinearPairing E EStar 𝕜] [HasContinuousPairing E EStar 𝕜]

local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.1 characterizes when the Fenchel conjugate `f*` of a closed
  convex function is finite everywhere.
- `core/canonical`: the project owner abstractions already present are `convexConjugate` for the
  conjugate, written on the theorem surface by the chapter notation `f⋆`, and
  `Function.IsCofinite` for Rockafellar's co-finite condition.
- `bridge/view`: on the chapter-facing codomain `WithBotTop 𝕜`, the textbook phrase
  "`f*` is finite at every point" is rendered intrinsically by the pointwise strict bounds
  `⊥ < f⋆ xStar` and `f⋆ xStar < ⊤` on the paired dual carrier `EStar`. This implies
  `dom(f⋆) = Set.univ`, but the converse alone would allow the spurious value `-∞`.

Domain-style sampling used here:
- `convexConjugate` and the chapter notation `f⋆`;
- `Function.IsCofinite`;
- `Function.IsClosedProperConvex`;
- `Function.isProper_iff`.
- Theorem 12.2's owner equivalence `Function.IsConvex.convexConjugate_isProper_iff`.

Primitive data vs derived API:
- primitive inputs: the function `f` together with the source hypotheses that `f` is closed and
  convex;
- derived API: the equivalence between pointwise finite-valuedness of the conjugate and
  co-finiteness.

Layer target: `source-facing`, stated directly in the canonical project language of Fenchel
conjugation and the already introduced co-finite predicate, without adding a surrogate domain
wrapper. The project owner `Function.IsClosedProperConvex` is deliberately not used as the public
hypothesis package here, because it would strengthen the source-facing statement by adding
properness; `Function.IsCofinite` remains the canonical owner on the conclusion side.
-/

/- `EStar` carries no topological assumptions here; the theorem surface uses only the
paired-linear owner layer.
-/

-- Proof sketch: first translate textbook finiteness of `f*` into the intrinsic pointwise bounds
-- `⊥ < f⋆ xStar ∧ f⋆ xStar < ⊤`, not merely the condition `< ⊤`. The support-function description
-- of the finite-value set
-- `dom(f⋆)` and the recession characterization from
-- Text 13.3.1 identify the everywhere-defined part with co-finiteness, while the lower bound
-- `⊥ < f⋆ xStar` rules out the spurious `-∞` case and hence matches the textbook meaning of
-- "finite".
/-- Corollary 13.3.1: for a closed convex function on a finite-dimensional topological vector space
over an ordered scalar field, paired continuously and linearly with a dual carrier `EStar`, the
Fenchel conjugate `f⋆` takes finite values at every point if and only if the function is
co-finite. -/
theorem convexConjugate_finite_everywhere_iff_isCofinite
    (f : E → WithBotTop 𝕜) (hf_convex : f.IsConvex 𝕜) (hf_closed : LowerSemicontinuous f) :
    (∀ xStar : EStar, ⊥ < f⋆ xStar ∧ f⋆ xStar < ⊤) ↔ IsCofinite[𝕜] f := sorry

end

/-! ### Text_13_3_1 (from Chap03) -/
section

universe u v w

open scoped Rockafellar

variable {𝕜 : Type u} {E : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [TopologicalSpace E] [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLattice α] [SMul 𝕜 α]
variable [TopologicalSpace (WithTopBot α)]

namespace Function

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.3.1 introduces the property that a convex function is co-finite.
- `core/canonical`: the relevant owner predicates already present in the project are
  `Function.IsClosedProperConvex` for the closed proper convex part and
  `Function.recessionFunction` for Rockafellar's recession function `f₀⁺`.
- `bridge/view`: the textbook phrase "epi f contains no non-vertical half-lines" is rendered by
  the recession condition `(f₀⁺) y = ⊤` for every nonzero direction `y`.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`;
- `Function.isClosedProperConvex_iff`;
- `Function.IsProper`;
- `Function.recessionFunction`;
- `Function.recessionFunction_apply`.

Primitive data vs derived API:
- primitive source-facing data: the intrinsic recession-domain condition
  `dom(f₀⁺) ⊆ {0}`, equivalent to ruling out non-vertical recession directions;
- derived API: the closed/proper/convex package, already owned upstream by
  `Function.IsClosedProperConvex`, and the pointwise nonzero-direction formula
  `f₀⁺ y = ⊤`.

Layer target: this item stays `source-facing`, but it should be expressed as the Chapter 3 owner
predicate for closed proper convexity together with the additional recession clause, not as an
coordinate-model-specific parallel bundle of the same fields. The ambient owner layer is the same
topological `𝕜`-module layer already used by `Function.IsClosedProperConvex` and
`recessionFunction`; textbook coordinate readings remain downstream specializations.
-/

/-- Text 13.3.1: a `WithTopBot α`-valued function on a topological `𝕜`-module is co-finite
when it is closed proper convex and its recession function satisfies `f₀⁺(y) = +∞` for every
nonzero direction `y`, equivalently when `epi f` contains no non-vertical half-lines. -/
@[mk_iff isCofinite_iff]
class IsCofinite (f : E → WithTopBot α) : Prop extends IsClosedProperConvex[𝕜] f where
  dom_recessionFunction_subset_zero : dom ((f)₀⁺) ⊆ ({0} : Set E)

local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

namespace IsCofinite

/-- Co-finiteness implies the nonzero-direction recession formula `f₀⁺ y = ⊤`. -/
theorem recession_eq_top {f : E → WithTopBot α} (hf : IsCofinite[𝕜] f)
    (y : E) (hy : y ≠ 0) :
    ((f)₀⁺) y = ⊤ := by
  have hy_not_mem : y ∉ dom(((f)₀⁺)) := by
    intro hy_mem
    have hy_zero : y = 0 := by
      simpa using hf.dom_recessionFunction_subset_zero hy_mem
    exact hy hy_zero
  have hy_not_lt : ¬ ((f)₀⁺) y < ⊤ := by
    intro hy_lt
    exact hy_not_mem (mem_effectiveDomain.mpr hy_lt)
  exact le_antisymm le_top (le_of_not_gt hy_not_lt)

end IsCofinite

namespace IsClosedProperConvex

/-- For a closed proper convex function, co-finiteness is exactly the added recession clause
`f₀⁺ y = ⊤` on every nonzero direction. -/
theorem isCofinite_iff_forall_ne_zero_recession_eq_top
    {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsCofinite[𝕜] f ↔ ∀ y : E, y ≠ 0 → ((f)₀⁺) y = ⊤ := by
  constructor
  · intro h y hy
    exact h.recession_eq_top y hy
  · intro h
    exact
      { toIsClosedProperConvex := hf
        dom_recessionFunction_subset_zero := by
          intro y hy_dom
          have hy0 : y = 0 := by
            by_contra hy0
            have hy_top : ((f)₀⁺) y = ⊤ := h y hy0
            have hy_not_mem : y ∉ dom(((f)₀⁺)) := by
              simpa [mem_effectiveDomain, hy_top]
            exact hy_not_mem hy_dom
          simp [hy0] }

/-- Backward-compatible short name for
`isCofinite_iff_forall_ne_zero_recession_eq_top`. -/
theorem isCofinite_iff {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsCofinite[𝕜] f ↔ ∀ y : E, y ≠ 0 → ((f)₀⁺) y = ⊤ :=
  isCofinite_iff_forall_ne_zero_recession_eq_top (𝕜 := 𝕜) (f := f) hf

/-- For a closed proper convex function, co-finiteness is equivalent to saying the effective
domain of the recession function is contained in `{0}`. This is the intrinsic owner-level form of
the nonzero-direction recession clause. -/
theorem isCofinite_iff_dom_recessionFunction_subset_zero
    {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f) :
    IsCofinite[𝕜] f ↔ dom(((f)₀⁺)) ⊆ ({0} : Set E) := by
  constructor
  · intro h
    exact h.dom_recessionFunction_subset_zero
  · intro h
    exact
      { toIsClosedProperConvex := hf
        dom_recessionFunction_subset_zero := h }

end IsClosedProperConvex

/-- Co-finiteness unfolds to closed proper convexity plus the nonzero-direction recession
formula. -/
theorem isCofinite_iff_isClosedProperConvex_and_forall_ne_zero_recession_eq_top
    {f : E → WithTopBot α} :
    IsCofinite[𝕜] f ↔
      IsClosedProperConvex[𝕜] f ∧ ∀ y : E, y ≠ 0 → ((f)₀⁺) y = ⊤ := by
  constructor
  · intro hf
    exact ⟨hf.toIsClosedProperConvex, fun y hy => hf.recession_eq_top y hy⟩
  · rintro ⟨hf_closed, hrec⟩
    exact
      (IsClosedProperConvex.isCofinite_iff_forall_ne_zero_recession_eq_top
        (𝕜 := 𝕜) (f := f) hf_closed).2 hrec

end Function

end

/-! ### Corollary_13_3_2 (from Chap03) -/
section

variable {𝕜 : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [HasLinearPairing E E 𝕜]

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.2 characterizes when `dom f*` is an affine set for a closed
  proper convex function `f`.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsClosedProperConvex`, the Chapter 13 support-function owner
  `supportFunction`, the support-asymmetry criterion on `dom(f⋆)`, the effective-domain
  support/recession bridge from `Theorem_13_3`, and the recession-function owner
  `Function.recessionFunction` written in this chapter as `f0⁺`.
- `bridge/view`: the textbook phrase `dom f*` is rendered by the chapter owner notation
  `dom(f⋆)`, while the phrase "is an affine set" is rendered by the affine-span fixed-point
  owner equation `(affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆)`.

Domain-style sampling used here:
- `supportFunction` from Chapter 1's owner declarations;
- the support-asymmetry affine criterion for a convex set, specialized in this file to `dom(f⋆)`;
- `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`.
- `Function.IsClosedProperConvex` from `Text_12_3_6`.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot 𝕜`;
- primitive owner-side data: the convex-set support-asymmetry owner criterion;
- derived owner-side data: convexity of `dom(f⋆)`, supplied canonically by
  `Function.isConvex_convexConjugate`;
- derived API: the source-facing closed-proper-convex specialization obtained by rewriting
  `δᵛ(· | dom(f⋆))` as `f0⁺` via `Theorem_13_3`.

Layer target: this item stays `source-facing`, with a pairing-level support-function theorem as
the primitive public owner surface and the `f0⁺` statement as a bridge specialization.
-/

/-- Canonical support-asymmetry affine criterion on a convex set. -/
theorem affineSpan_eq_self_iff_supportFunction_eq_top_of_support_asymmetry
    {C : Set E} (hC : Convex 𝕜 C) :
    (affineSpan 𝕜 C : Set E) = C ↔
      ∀ y : E,
        -δᵛ[WithTopBot 𝕜](-y | C) ≠
            δᵛ[WithTopBot 𝕜](y | C) →
          δᵛ[WithTopBot 𝕜](y | C) = ⊤ := by
  sorry

/-- Primitive owner form for Corollary 13.3.2: `dom(f⋆)` is affine exactly when every
support-asymmetric direction has support value `+∞`. -/
theorem effectiveDomain_convexConjugate_affine_iff_supportFunction_eq_top_of_support_asymmetry
    (f : E → WithTopBot 𝕜) :
    (affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆) ↔
      ∀ y : E,
        -δᵛ[WithTopBot 𝕜](-y | dom(f⋆)) ≠
            δᵛ[WithTopBot 𝕜](y | dom(f⋆)) →
          δᵛ[WithTopBot 𝕜](y | dom(f⋆)) = ⊤ := by
  have hdom_convex : Convex 𝕜 dom(f⋆) := by
    simpa using ((Function.isConvex_convexConjugate f).convex_dom)
  simpa using
    (affineSpan_eq_self_iff_supportFunction_eq_top_of_support_asymmetry
      (C := dom(f⋆)) hdom_convex)

section Bridge

variable [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

-- Proof sketch: apply the primitive support-function theorem above and rewrite the
-- support-function owner to `f0⁺` via the supplied bridge.
/-- Bridge form for Corollary 13.3.2: if the support function of `dom(f⋆)`
agrees with the recession function `f0⁺`, then `dom(f⋆)` is affine exactly when every
support-asymmetric primal direction already has recession value `+∞`. -/
private theorem
    effectiveDomain_convexConjugate_affine_iff_recessionFunction_eq_top_of_asymmetry_of_bridge
    (f : E → WithTopBot 𝕜)
    (hsupport :
      (δᵛ[WithTopBot 𝕜](· | dom(f⋆)) : E → WithTopBot 𝕜) = (f₀⁺ : E → WithTopBot 𝕜)) :
    (affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆) ↔
      ∀ y : E, -(f₀⁺ (-y)) ≠ f₀⁺ y → f₀⁺ y = ⊤ := by
  constructor
  · intro haff y hy
    have hy_support :
        -δᵛ[WithTopBot 𝕜](-y | dom(f⋆)) ≠
            δᵛ[WithTopBot 𝕜](y | dom(f⋆)) := by
      simpa [hsupport] using hy
    have htop_support :
        δᵛ[WithTopBot 𝕜](y | dom(f⋆)) = (⊤ : WithTopBot 𝕜) :=
      (effectiveDomain_convexConjugate_affine_iff_supportFunction_eq_top_of_support_asymmetry
        (f := f)).1 haff y hy_support
    simpa [hsupport] using htop_support
  · intro hrec
    refine
      (effectiveDomain_convexConjugate_affine_iff_supportFunction_eq_top_of_support_asymmetry
        (f := f)).2 ?_
    intro y hy_support
    have hy_rec : -(f₀⁺ (-y)) ≠ f₀⁺ y := by
      simpa [hsupport] using hy_support
    have htop_rec : f₀⁺ y = (⊤ : WithTopBot 𝕜) := hrec y hy_rec
    simpa [hsupport] using htop_rec

-- Proof sketch: by Theorem 13.3, `f0⁺` is the support function of `dom(f⋆)`. Apply the bridge
-- theorem above and rewrite the support-function owner to `f0⁺`.
/-- Corollary 13.3.2: for a closed proper convex function `f`, the effective domain of `f*` is an
affine set exactly when every direction where the recession function `f0⁺` fails the support
symmetry relation `-f0⁺(-y) = f0⁺ y` already has recession value `+∞`. -/
theorem effectiveDomain_convexConjugate_affine_iff_recessionFunction_eq_top_of_support_asymmetry
    (f : E → WithTopBot 𝕜) (hf : IsClosedProperConvex[𝕜] f) :
    (affineSpan 𝕜 dom(f⋆) : Set E) = dom(f⋆) ↔
      ∀ y : E, -(f₀⁺ (-y)) ≠ f₀⁺ y → f₀⁺ y = ⊤ := by
  have hsupport :
      (δᵛ[WithTopBot 𝕜](· | dom(f⋆)) : E → WithTopBot 𝕜) = (f₀⁺ : E → WithTopBot 𝕜) := by
    simpa using
      supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction
        (f := f) hf
  exact
    effectiveDomain_convexConjugate_affine_iff_recessionFunction_eq_top_of_asymmetry_of_bridge
      (f := f) hsupport

end Bridge

end

/-! ### Text_13_3_2 (from Chap03) -/
section

universe u v w

open Bornology

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [SMul 𝕜 E]
variable {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [SMul 𝕜 α]
variable [TopologicalSpace (WithTopBot α)]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.3.2 says that a closed proper convex function is co-finite whenever
  its domain is bounded.
- `core/canonical`: the owner predicates already fixed in this chapter are
  `Function.IsClosedProperConvex`, the co-finite owner predicate `Function.IsCofinite`, and the
  effective-domain owner `dom(·)`.
- `bridge/view`: boundedness of the source-visible domain is rendered canonically by
  `IsBounded dom(f)`, while the recession-side criterion is supplied by the chapter
  recession owner theorem.

Domain-style sampling used here:
- `Function.IsClosedProperConvex` from `Text_12_3_6`;
- `Function.IsCofinite` from `Text_13_3_1`;
- `effectiveDomain` from `Definition_4_4`;
- `recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain` from
  `Remark_9_2_0_2`;

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot α`;
- owner hypotheses: closed proper convexity of `f` and boundedness of its effective domain
  `dom(f)`;
- derived API: the co-finite conclusion, expressed by the owner predicate from Text 13.3.1.

Layer target: this item stays `source-facing`, but both its hypothesis package and its conclusion
are stated directly using the chapter owner predicates rather than re-expanding them locally.
Ambient refinement: the only genuinely metric input is boundedness of `dom(f)`, so the theorem is
stated on an intrinsic `RCLike` normed-space ambient layer `[NormedSpace K E]`, while the
closed/proper/convex and co-finite owners remain scalar-generic in `𝕜`.
-/

namespace Function.IsClosedProperConvex

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsCofinite[" 𝕜 "]" => Function.IsCofinite (𝕜 := 𝕜)

/-- Text 13.3.2: a closed proper convex function is co-finite whenever its effective domain
`dom(f)` is bounded. -/
-- Proof sketch: boundedness of the effective domain rules out every nonzero recession
-- direction, because any half-line `x + t • y` with `y ≠ 0` would be unbounded. The previous text
-- identifies co-finiteness with the condition `(f0⁺) y = ⊤` for all nonzero `y`,
-- and the remaining closed/proper/convex hypotheses are already packaged by the owner predicate
-- `Function.IsClosedProperConvex`.
theorem isCofinite_of_bounded_effectiveDomain
    {K : Type*} [RCLike K] [NormedSpace K E]
    {f : E → WithTopBot α} (hf : IsClosedProperConvex[𝕜] f)
    (hdom_bounded : IsBounded dom(f)) :
    IsCofinite[𝕜] f := by
  have hcof := hf.isCofinite_iff_dom_recessionFunction_subset_zero
  rw [hcof]
  intro y hy_dom
  have hy0 : y = 0 := by
    by_contra hy0
    have hy_top : recessionFunction f y = ⊤ :=
      recessionFunction_eq_top_of_ne_zero_of_bounded_effectiveDomain
        f hf.proper.nonempty_dom hdom_bounded y hy0
    have hy_not_mem : y ∉ dom(recessionFunction f) := by
      simpa [mem_effectiveDomain, hy_top]
    exact hy_not_mem hy_dom
  simp [hy0]

end Function.IsClosedProperConvex

end

/-! ### Corollary_13_3_3 (from Chap03) -/
noncomputable section

section

open Bornology
open scoped Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.3 characterizes boundedness of `dom f⋆` for a closed proper
  convex function by global finiteness and a norm-Lipschitz bound, and under that boundedness
  hypothesis identifies the least admissible Lipschitz constant.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  the chapter notation `f⋆`, the chapter effective-domain owner `dom(f⋆)`, the chapter owner
  predicate `f.IsClosedProperConvex`, together with `Bornology.IsBounded`, `LipschitzWith`, and
  `IsLeast`.
- `bridge/view`: the textbook absolute-difference inequality
  `|f z - f x| ≤ α ‖z - x‖` is expressed by `LipschitzWith α (fun x ↦ (f x).toReal)`, while
  under the standing closed-proper-convex hypothesis, the textbook finiteness condition on `f`
  is rendered by `∀ x, f x < ⊤`.

Domain-style sampling used here:
- the conjugate owner notation `f⋆` from Chapter 3;
- the support-function owner theorem
  `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`;
- the chapter effective-domain notation `dom(f)` and its conjugate specialization `dom(f⋆)`;
- the finite-dimensional owner theorem
  `exists_lipschitzWith_of_recessionFunction_finite_everywhere` from `Theorem_10_5`;
- mathlib's canonical boundedness predicate `IsBounded`;
- mathlib's canonical global-Lipschitz owner `LipschitzWith`.
- `IsLeast` for the least admissible Lipschitz constant under the bounded-domain hypothesis.

Primitive data vs derived API:
- primitive input: the function `f : E → EReal`;
- owner hypothesis: `f.IsClosedProperConvex`, packaging the convexity, properness, and lower
  semicontinuity needed by `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction`;
- additional source-facing hypothesis for the least-constant clause: boundedness of `dom(f⋆)`;
- derived API: the Lipschitz characterization of boundedness and the least admissible Lipschitz
  constant, expressed directly as the supremum of the norm image of that effective domain.

Ambient refinement: the supporting owner declarations already live on arbitrary finite-dimensional
real inner-product spaces, so this corollary is stated at that intrinsic level rather than the
coordinate model `EuclideanSpace ℝ (Fin n)`.

Layer target: `source-facing`, stated directly in the canonical conjugate/effective-domain owner
language without introducing a surrogate wrapper for `dom f⋆`.
-/

variable (f : E → EReal)

-- Proof sketch: reduce boundedness of `dom f⋆` to the support-function estimate
-- `supportFunction (dom f⋆) y ≤ α ‖y‖`, use Theorem 13.3 to rewrite that support function as the
-- recession function of `f`, and then apply Corollary 8.5.1 together with the support-function
-- description of the closed unit ball to translate the estimate into the stated global Lipschitz
-- condition on `f`.
/-- Corollary 13.3.3: for a closed proper convex function `f`, the effective domain
`dom f⋆ = dom(f⋆) = {xStar | f⋆ xStar < ⊤}` is bounded if and only if `f` is finite everywhere
and there exists a nonnegative real number `α` such that `|f z - f x| ≤ α ‖z - x‖` for all `x`
and `z`, expressed canonically by `LipschitzWith α (fun x ↦ (f x).toReal)`. -/
theorem bounded_effectiveDomain_convexConjugate_iff_finiteValued_exists_lipschitzWith
    (hf : f.IsClosedProperConvex) :
    IsBounded dom((f⋆ : E → EReal)) ↔
      (∀ x, f x < ⊤) ∧ ∃ α : NNReal, LipschitzWith α (fun x ↦ (f x).toReal) := sorry

-- Proof sketch: by the first theorem, boundedness of `dom f⋆` is equivalent to existence of a
-- global Lipschitz constant. For each such `α`, Corollary 13.1.1 identifies the domination
-- `supportFunction (dom f⋆) ≤ supportFunction (α • B)` with inclusion `dom f⋆ ⊆ α • B`, so the
-- admissible constants are exactly the upper bounds for the norms of points in `dom f⋆`. Their
-- least element is therefore the supremum of the norm image of `dom f⋆`.
/-- The least nonnegative global Lipschitz bound for `f`, when `dom f⋆` is bounded, is the
supremum of `‖x⋆‖` over all `x⋆ ∈ dom f⋆`. -/
theorem isLeast_lipschitzWith_sSup_norm_image_effectiveDomain_convexConjugate
    (hf : f.IsClosedProperConvex) (hdom_bounded : IsBounded dom((f⋆ : E → EReal))) :
    IsLeast {α : NNReal | LipschitzWith α (fun x ↦ (f x).toReal)}
      (sSup ((‖·‖₊) '' dom((f⋆ : E → EReal)))) := sorry

end

/-! ### Theorem_13_3 (from Chap03) -/
noncomputable section

universe u v

section PairingSwapped

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 13.3 identifies the support function of `dom f` with the recession
  function of `f*`, and in the closed case identifies the support function of `dom f*` with the
  recession function of `f`.
- `core/canonical`: the owner abstractions already present in the project are `supportFunction`,
  `convexConjugate`, `Function.recessionFunction`, `Function.IsConvex`,
  `Function.IsProper`, and `Function.IsClosedProperConvex`, with the source-facing theorem surface
  written using the chapter notation `δᵛ(· | ·)` and the object-prefix predicates `f.IsConvex`
  and `f.IsProper`.
- `bridge/view`: for `WithTopBot 𝕜`-valued functions, Rockafellar's `dom f` is the chapter's
  established
  effective-domain set `dom(f) = {x : X | f x < ⊤}`, so `dom f*` is correspondingly `dom(f⋆)`.

Domain-style sampling used here:
- `supportFunction` from Definition 4.8.2;
- `Function.recessionFunction` from Corollary 8.5.1;
- `convexConjugate` from Definition 12.2;
- the closed-case biconjugacy theorem `Function.IsClosedProperConvex.biconjugate_eq`.

Primitive data vs derived API:
- primitive input: a function `f : X → WithTopBot 𝕜`;
- owner hypotheses: `f.IsConvex` and `f.IsProper` for clause (1);
- derived API: clause (2), obtained from clause (1) applied to `f⋆` together with closed proper
  convex biconjugacy.

Layer target: this item stays `source-facing`, with clause (1) stated on the swap-compatible
paired-space owner layer and clause (2) on the finite-dimensional continuous linear self-pairing
layer where the current biconjugacy dependency lives.

Codomain/scalar canonicalization note for this file:
- clause (1) is stated directly on the canonical codomain `WithTopBot 𝕜` at the pairing layer;
- clause (2) is stated on the finite-dimensional scalar-generic layer where the reused closed
  proper convex biconjugacy route is already available in this dependency chain.
-/
variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X] [HasPairing X Y 𝕜]
variable [AddCommMonoid Y] [HasPairing Y X 𝕜]
variable [HasPairingSwap X Y 𝕜]
local instance : HasPairing X Y (WithTopBot 𝕜) := instHasPairingWithBotTop
local instance : HasPairing Y X (WithTopBot 𝕜) := instHasPairingWithBotTop
variable (f : X → WithTopBot 𝕜)

-- Proof sketch: represent `f*` as the pointwise supremum of the affine functions
-- `xStar ↦ ⟪x, xStar⟫ - μ` coming from points `(x, μ)` of the epigraph of `f`. The recession
-- function of such an affine function is the linear map `xStar ↦ ⟪x, xStar⟫`, so the recession
-- function of `f*` is the pointwise supremum of those linear maps over `x ∈ dom(f)`. That
-- supremum is exactly `δᵛ(· | dom(f))`.
private theorem
    supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate_of_pairing_swap_core
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    δᵛ(· | dom(f)) = (f⋆)₀⁺ := by
  sorry

/-- Theorem 13.3 (1), pairing-owner form: on a swap-compatible dual pairing, the support function
of the effective domain `dom(f)` of a proper convex function `f` equals the recession function of
its Fenchel conjugate `f⋆`. -/
theorem supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    δᵛ(· | dom(f)) = (f⋆)₀⁺ := by
  simpa using
    supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate_of_pairing_swap_core
      hf_convex hf_proper

end PairingSwapped

section PairingFiniteDimensional

open scoped Rockafellar

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithTopBot 𝕜) := instHasPairingWithBotTop
variable (f : E → WithTopBot 𝕜)

-- Proof sketch: apply clause (1) to `convexConjugate f`. Under the packaged closed proper convex
-- hypothesis `f.IsClosedProperConvex`, biconjugacy gives `f⋆⋆ = f`, so `δᵛ(· | dom(f⋆))`
-- identifies with `f0⁺`.
/-- Theorem 13.3 (2): if `f` is closed as well as proper convex, then the support function of
`dom(f⋆)` is the recession function `f₀⁺`. This clause is stated at the finite-dimensional
continuous linear self-pairing layer and uses closed proper convex biconjugacy. -/
theorem supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction
    (hf : f.IsClosedProperConvex) :
    δᵛ(· | dom(f⋆)) = f₀⁺ := by
  have hfirst :
      δᵛ(· | dom(f⋆)) = (f⋆⋆)₀⁺ := by
    simpa using
      supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
        (f := f⋆) hf.convexConjugate.convex hf.convexConjugate.proper
  have hbiconj : f⋆⋆ = f := by
    simpa using hf.biconjugate_eq
  have hrec : (f⋆⋆)₀⁺ = f₀⁺ := by
    simpa using congrArg Function.recessionFunction hbiconj
  exact hfirst.trans hrec

end PairingFiniteDimensional

/-! ### Corollary_13_3_4 (from Chap03) -/
noncomputable section

open scoped RealInnerProductSpace Rockafellar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 13.3.4 studies the translated function
  `g(x) = f x - ⟪x, x⋆⟫` for a closed proper convex function `f` and characterizes the position of
  `x⋆` relative to `dom f⋆` in terms of the recession function `g₀⁺`.
- `core/canonical`: the owner abstractions already present in the project are
  `isClosedProperConvexFunction`, `convexConjugate`, `ConvexERealFunction.recessionFunction`,
  `Function.constancySpace`, `closure`, `intrinsicInterior ℝ`, `interior`, and
  `affineSpan`.
- `bridge/view`: Rockafellar's `dom f⋆` is rendered by the chapter's canonical effective-domain
  owner `dom(f⋆)`, while the translated function `g` is written directly as the affine
  perturbation `fun x ↦ f x - (⟪x, xStar⟫ : EReal)`.

Domain-style sampling used here:
- `mem_closure_iff_dual_le_supportFunction` and
  `mem_intrinsicInterior_iff_mem_closure_and_lt_of_support_asymmetry` from `Theorem_13_1.lean`;
- `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from
  `Theorem_13_3.lean`;
- `convexConjugate_affineChange` from `Theorem_12_3.lean`;
- `Function.constancySpace` and `Function.mem_constancySpace_iff` from
  `Definiton_8_7_0.lean`;
- the topological owners `closure`, `intrinsicInterior ℝ`, `interior`, and `affineSpan`.

Primitive data vs derived API:
- primitive inputs: the function `f` and the fixed vector `xStar`;
- derived owner hypothesis: `isClosedProperConvexFunction f`;
- source-facing core object: the translated function `g(x) = f x - ⟪x, x⋆⟫`;
- derived API: the four domain-position criteria for `xStar`.

Layer target: `source-facing`, stated directly in the canonical project language without replacing
the translated function by an existential or surrogate package.
-/

variable (f : E → EReal) (xStar : E)
variable (hf : f.IsClosedProperConvex)

local notation "g" => fun x ↦ f x - (⟪x, xStar⟫ : EReal)
local notation "g0⁺" => ((g)₀⁺)

-- Proof sketch: let `g := fun x ↦ f x - (⟪x, xStar⟫ : EReal)`. The canonical affine-conjugation
-- owner `convexConjugate_affineChange` identifies the conjugate
-- domain of `g` as the translate `dom(f⋆) - xStar`. Theorem 13.3 identifies the
-- support function of that translated domain with `g0⁺`, and Theorem 13.1's
-- closure criterion at the origin rewrites `0 ∈ closure (dom g⋆)` as pointwise nonnegativity of
-- `g₀⁺`.
/-- Corollary 13.3.4 (1): clause (a). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `cl (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` is nonnegative in every direction. -/
theorem mem_closure_effectiveDomain_convexConjugate_iff_nonneg_recessionFunction_inner_sub
    :
    xStar ∈ closure (dom((f⋆ : E → EReal))) ↔
      ∀ y : E, (0 : EReal) ≤ g0⁺ y := sorry

-- Proof sketch: keep `g := fun x ↦ f x - (⟪x, xStar⟫ : EReal)` and translate `dom g⋆` back
-- to `dom f⋆` as in part (a). The support-function formula from Theorem 13.3 gives
-- `supportFunction (dom g⋆) = g₀⁺`, while the relative-interior criterion from Theorem 13.1 at
-- the origin says exactly that every direction is either a zero direction in the owner constancy
-- space `Function.constancySpace g0⁺` or has strictly positive value.
/-- Corollary 13.3.4 (2): clause (b). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `ri (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` is strictly positive in every direction except the zero directions in
`Function.constancySpace g₀⁺`. -/
theorem
    mem_intrinsicInterior_effectiveDomain_convexConjugate_iff_pos_or_zero_on_constancySpace_recessionFunction_inner_sub
    :
    xStar ∈ intrinsicInterior ℝ (dom((f⋆ : E → EReal))) ↔
      ∀ y : E,
        (0 : EReal) < g0⁺ y ∨
          (y ∈ Function.constancySpace g0⁺ ∧ g0⁺ y = (0 : EReal)) := sorry

-- Proof sketch: again translate to the origin for `dom g⋆`. Theorem 13.1 identifies interior
-- membership of a convex set with strict support-function positivity on every nonzero direction;
-- using Theorem 13.3 to replace that support function by `g₀⁺` yields the displayed criterion.
/-- Corollary 13.3.4 (3): clause (c). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `int (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` is strictly positive in every nonzero direction. -/
theorem mem_interior_effectiveDomain_convexConjugate_iff_pos_recessionFunction_inner_sub_of_ne_zero
    :
    xStar ∈ interior (dom((f⋆ : E → EReal))) ↔
      ∀ y : E, y ≠ 0 →
        (0 : EReal) < g0⁺ y := sorry

-- Proof sketch: let `g := fun x ↦ f x - (⟪x, xStar⟫ : EReal)` as above. The affine-span
-- criterion for the origin in a convex set says `0 ∈ aff (dom g⋆)` exactly when the support
-- interval of `dom g⋆` collapses only at `0`: whenever the lower and upper support values agree,
-- that common value must be `0`. Theorem 13.3 replaces the support function of `dom g⋆` by `g₀⁺`,
-- yielding the displayed support-symmetry criterion for the translated recession function.
/-- Corollary 13.3.4 (4): clause (d). For a closed proper convex function `f`, a fixed vector
`x⋆` lies in `aff (dom f⋆)` exactly when the recession function `g₀⁺` of
`g(x) = f x - ⟪x, x⋆⟫` has the property that every direction where the support symmetry relation
`-g₀⁺(-y) = g₀⁺ y` holds actually has common value `0`. -/
theorem mem_affineSpan_effectiveDomain_convexConjugate_iff_zero_of_support_symmetry_recessionFunction_inner_sub
    :
    xStar ∈ affineSpan ℝ (dom((f⋆ : E → EReal))) ↔
      ∀ y : E,
        -(g0⁺ (-y)) = g0⁺ y → g0⁺ y = (0 : EReal) := sorry

end
