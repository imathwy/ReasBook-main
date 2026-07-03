import Mathlib
import Mathlib.Order.WithBotTop
import Mathlib.Tactic.Recall
import Mathlib.Topology.Semicontinuity.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_29_1 (from Chap06) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.1 takes a convex bifunction `F`, assumes that the optimal value
  of the associated generalized convex program is finite, and draws six source-facing
  consequences: existence of the directional derivative of `inf F` at `0`, convexity and positive
  homogeneity of that derivative profile, closedness and convexity of the Kuhn--Tucker vector set
  in the canonical dual, and the support-function / lower-semicontinuous-hull identification for
  that dual-side set.
- `core/canonical`: the relevant owners are already present as `perturbationFunction F`,
  `optimalValue F`, `kuhnTuckerVectorSet F`, the dual-valued subdifferential owner
  `∂[StrongDual ℝ U] (perturbationFunction F) (0)`, `HasDirectionalDerivativeAt`,
  `directionalDerivativeAt`, `δᵛ(· | ·)`, and `cl(·)`.
- `bridge/view`: the source phrase `(inf F)(0; u)` is rendered by the canonical owner
  `directionalDerivativeAt (perturbationFunction F) 0 u`; the Kuhn--Tucker vectors are surfaced
  through the existing owner `kuhnTuckerVectorSet F` rather than by repeating a raw set literal,
  and the Fréchet-Riesz self-dual specialization is deliberately not taken as the main public
  layer here.

Domain-style sampling used here:

- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.kuhnTuckerVectorSet` from `Definition_6_29_19`;
- `Bifunction.perturbationFunction_isConvex` and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`
  from `Theorem_6_29_1`;
- `HasDirectionalDerivativeAt`, `isConvex_directionalDerivativeAt_of_finite_point`, and
  `positivelyHomogeneous_directionalDerivativeAt_of_finite_point` from `Chap05.Theorem_23_1`;
- `_root_.subdifferentialAt_isClosed` and `_root_.subdifferentialAt_convex` from
  `Chap05.Definition_23_0_6`;
- `δᵛ(· | ·)` and `cl(·)` from Chapters 1 and 2.
-/

section DirectionalDerivative

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

variable {F : U → X → WithBotTop 𝕜}

local notation "p" => perturbationFunction F

-- Proof sketch: use `perturbationFunction_isConvex` to show that `perturbationFunction F` is
-- convex, read the finiteness hypothesis as finiteness of `perturbationFunction F` at `0`, and
-- then apply `hasDirectionalDerivativeAt_sInf_directionalDifferenceQuotientAt` at the base
-- point `0`.
/-- Corollary 6.29.1 (1): if the optimal value of the generalized convex program attached to a
convex bifunction `F` is finite, then the one-sided directional derivative of
`perturbationFunction F` at `0` exists in every direction. -/
theorem hasDirectionalDerivativeAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤)
    (u : U) :
    HasDirectionalDerivativeAt p (0 : U) u (directionalDerivativeAt p (0 : U) u) := sorry

-- Proof sketch: first obtain convexity of `perturbationFunction F` from
-- `perturbationFunction_isConvex`; then apply `isConvex_directionalDerivativeAt_of_finite_point`
-- at `0`, using finiteness of `optimalValue F = perturbationFunction F 0`.
/-- Corollary 6.29.1 (2): when the optimal value is finite, the directional-derivative profile
`u ↦ directionalDerivativeAt (perturbationFunction F) 0 u` is convex. -/
theorem isConvex_directionalDerivativeAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (directionalDerivativeAt p (0 : U)).IsConvex 𝕜 := sorry

-- Proof sketch: the same convexity and finiteness input at `0` lets
-- `positivelyHomogeneous_directionalDerivativeAt_of_finite_point` apply to
-- `perturbationFunction F`.
/-- Corollary 6.29.1 (3): when the optimal value is finite, the directional-derivative
profile `u ↦ directionalDerivativeAt (perturbationFunction F) 0 u` is positively homogeneous. -/
theorem
    positivelyHomogeneous_directionalDerivativeAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (directionalDerivativeAt p (0 : U)).PositivelyHomogeneous 𝕜 := sorry

end DirectionalDerivative

section KuhnTuckerClosedConvex

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type (max u w)}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set UStar)

-- Proof sketch: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of the
-- dual-valued subdifferential of `perturbationFunction F` at `0`; closedness of that canonical
-- subdifferential then transfers to the reflected set.
/-- Corollary 6.29.1 (4): under finiteness of the optimal value, the Kuhn--Tucker vectors of `F`
form a closed subset of the paired dual perturbation space. -/
theorem isClosed_kuhnTuckerVectorSet_of_optimalValue_finite
    [TopologicalSpace UStar]
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    IsClosed (KT(F)) := sorry

-- Proof sketch: use the same subdifferential characterization of Kuhn--Tucker vectors and
-- transfer convexity from `_root_.subdifferentialAt (perturbationFunction F) 0` through negation
-- on the canonical dual.
/-- Corollary 6.29.1 (5): under finiteness of the optimal value, the Kuhn--Tucker vectors of `F`
form a convex subset of the paired dual perturbation space. -/
theorem convex_kuhnTuckerVectorSet_of_optimalValue_finite
    [AddCommMonoid UStar] [Module 𝕜 UStar]
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    Convex 𝕜 (KT(F)) := sorry

end KuhnTuckerClosedConvex

section KuhnTuckerSupportIdentity

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type (max u w)}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]

variable {F : U → X → WithBotTop 𝕜}

local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set UStar)
local notation "p" => perturbationFunction F

-- Proof sketch: identify the Kuhn--Tucker set with the negated subdifferential at `0`, rewrite
-- the support function of that reflected set in terms of the support function of the
-- subdifferential, and then use the Chapter 23 directional-derivative/support-function bridge at
-- the finite point `0` to express that support function as the lower-semicontinuous hull of the
-- reflected directional-derivative profile.
/-- Corollary 6.29.1 (6): under finiteness of the optimal value, the support function of the
dual-side Kuhn--Tucker vector set equals the lower-semicontinuous hull of the reflected
directional derivative `u ↦ directionalDerivativeAt (perturbationFunction F) 0 (-u)`. -/
theorem
    supportFunction_kuhnTuckerVectorSet_eq_cl_reflectedDirectionalDerivative_of_optimalValue_finite
    (hF : (Function.uncurry F).IsConvex 𝕜)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (δᵛ(· | KT(F)) : U → WithBotTop 𝕜) =
      cl(fun u ↦ directionalDerivativeAt p 0 (-u)) := sorry

end KuhnTuckerSupportIdentity

end Bifunction

/-! ### Definition_6_29_1 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v r

section

variable {U : Type u} {X : Type v} {α : Type r}

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: the opening definitions of §29 work with a bifunction
  `F : U → X → WithTopBot α` and the perturbation function `u ↦ inf_x F u x` attached to the
  associated generalized convex
  program.
- `core/canonical`: the project already owns the effective-domain operator `dom(·)` for
  `WithTopBot`-valued functions in Chapter 1, and for arbitrary ambient types it already owns
  the first-projection image operator `Function.linearImage (Prod.fst : U × X → U)`.
- `bridge/view`: the perturbation function is the pointwise infimum in the second variable, so
  it agrees with the Chapter 1 first-projection image operator;
  the source's consistency condition is then nonemptiness of the effective domain of the
  zero-slice `F 0`, equivalently membership of `0` in `dom(perturbationFunction F)` on the
  complete-lattice bridge layer.

Domain-style sampling used here:
- `Function.partialInfimum` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_7_2`;
- `Function.partialInfimum_apply` from the same file, which is the owner-side slice formula;
- `effectiveDomain` / `dom(·)` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4`;
- `mem_effectiveDomain` from the same file, which is the owner-side test `f x < ⊤`;
- `Function.linearImage_eq_sInf_image` from
  `ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7`.

Primitive data vs derived API:
- primitive source data: the bifunction `F`;
- source-facing owner: `perturbationFunction F`;
- core owner reused from Chapter 1: `partialInfimum (Function.uncurry F)`;
- derived API: the indexed-infimum evaluation formula, the first-projection linear-image bridge,
  and the complete-lattice consistency bridge to `dom(perturbationFunction F)`.

Layer target: `source-facing`. The perturbation function is a genuine named source object, but it
is implemented as the thin curried specialization of the existing Chapter 1 owner
`Function.partialInfimum` rather than by duplicating the raw `sInf` construction.
-/

section

variable [InfSet α]

/-- The perturbation function attached to a bifunction `F`, defined by taking the pointwise
infimum in the second variable. -/
abbrev perturbationFunction (F : U → X → α) : U → α :=
  partialInfimum (Function.uncurry F)

/-- Rockafellar's source-facing notation for the perturbation function `inf F`. -/
scoped[Rockafellar] notation "infᵇ(" F ")" => Bifunction.perturbationFunction F

/-- Evaluating the perturbation function at `u` gives the infimum of the slice `F u` over the
`X`-variable, written as the infimum of its range in `α`. -/
@[simp] theorem perturbationFunction_apply_eq_sInf_range
    (F : U → X → α) (u : U) :
    infᵇ(F) u = sInf (Set.range (F u)) := by
  simp [perturbationFunction]

/-- Evaluating the perturbation function at `u` is the indexed infimum `inf_x F u x`. -/
@[simp] theorem perturbationFunction_apply (F : U → X → α) (u : U) :
    infᵇ(F) u = ⨅ x, F u x := by
  rw [perturbationFunction_apply_eq_sInf_range, ← sInf_range]

/-- The perturbation function of a bifunction is exactly the image of `Function.uncurry F` under
the intrinsic first-coordinate projection map. -/
theorem perturbationFunction_eq_linearImage_fst (F : U → X → α) :
    infᵇ(F) = (Prod.fst : U × X → U) ◁ Function.uncurry F := by
  funext u
  rw [perturbationFunction_apply_eq_sInf_range, linearImage_eq_sInf_image]
  congr 1
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(u, x), by simp, rfl⟩
  · rintro ⟨⟨u', x⟩, hu', ha⟩
    dsimp at hu'
    subst hu'
    exact ⟨x, by simpa [Function.uncurry] using ha⟩

end

section

variable {β : Type r}
variable [Zero U] [Top β] [LT β]

/-- The generalized convex program attached to `F` is consistent when the unperturbed problem has
at least one feasible decision for the zero-perturbation slice, i.e. some `x` with
`F 0 x < ⊤`. -/
def IsConsistent (F : U → X → β) : Prop :=
  (dom(F 0)).Nonempty

@[simp] theorem isConsistent_iff_exists_lt_top (F : U → X → β) :
    IsConsistent F ↔ ∃ x : X, F 0 x < ⊤ := by
  simp [IsConsistent]

end

section

variable {β : Type r}
variable [Zero U] [CompleteLattice β]

@[simp] theorem isConsistent_iff_lt_top (F : U → X → β) :
    IsConsistent F ↔ infᵇ(F) 0 < ⊤ := by
  rw [isConsistent_iff_exists_lt_top]
  rw [perturbationFunction_apply]
  exact
    (iInf_lt_top : (⨅ x : X, F 0 x) < ⊤ ↔ ∃ x : X, F 0 x < ⊤).symm

@[simp] theorem isConsistent_iff_zero_mem_dom_perturbationFunction
    (F : U → X → β) :
    IsConsistent F ↔ (0 : U) ∈ dom(infᵇ(F)) := by
  rw [isConsistent_iff_lt_top, _root_.mem_effectiveDomain]

end

end Bifunction

end

/-! ### Lemma_6_29_1 (from Chap06) -/
noncomputable section

universe u v w

namespace OrdinaryConvexProgram

section

open scoped Rockafellar

variable {𝕜 : Type v} {E : Type u} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.1 says that the bifunction associated with an ordinary convex
  program is convex in the joint perturbation/decision variables.
- `core/canonical`: Chapter 6 already owns that bifunction as `P.perturbedProblem`, and Chapter 1
  already owns bifunction convexity as `Function.IsConvex 𝕜 (Function.uncurry F)`.
- `bridge/view`: this file should therefore state the lemma on the source-facing bifunction
  convexity notation `convᵇ[𝕜](P.perturbedProblem)` (definitionally
  `Function.IsConvex 𝕜 (Function.uncurry P.perturbedProblem)`); the explicit source constraint set
  and the split inequality/equality data stay in the owner `OrdinaryConvexProgram`, rather than
  being rebuilt as a second full-space wrapper API.

Domain-style sampling used here:
- `OrdinaryConvexProgram` from `Definition_6_28_1`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `Function.IsConvex` from `Chap01.Theorem_4_2` (via the Chapter 6 owner imports);
- `convᵇ[𝕜](·)` from `Definition_6_29_4`;
- `Function.toWithBotTopOn` as the canonical extended-value owner already used by
  `P.perturbedProblem`.

Primitive data vs derived API:
- primitive source data: the program `P`, which already packages the source constraint set, the
  objective on that set, the convex inequality family, and the affine equality family;
- derived API: bifunction convexity of `P.perturbedProblem`, written in source form
  `convᵇ[𝕜](P.perturbedProblem)`.

Layer target: `source-facing`, stated directly on the existing Chapter 6 owner.
-/

-- Proof sketch: unfold `P.perturbedProblem` as the canonical `+∞`-extension of the objective to
-- each perturbed feasible set. The base constraint set is convex by `P.constraintSet_convex`; the
-- perturbed inequality slices are convex by the convexity fields of `P`, and the perturbed
-- equality slices are affine by the affine fields of `P`. The graph-function decomposition into
-- the objective branch and the corresponding indicator terms is therefore convex termwise, and so
-- is their sum.
/-- Lemma 6.29.1: the graph function of the perturbed problem associated with an ordinary convex
program is convex on the product of perturbation parameters and decision variables. -/
theorem uncurry_perturbedProblem_isConvex :
    convᵇ[𝕜](P.perturbedProblem) := sorry

end

end OrdinaryConvexProgram

/-! ### Proposition_6_29_1 (from Chap06) -/
noncomputable section

universe u v w z

section

open Function

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.29.1 says that convexity of a graph function on a product space
  implies convexity of each slice obtained by fixing the first variable.
- `core/canonical`: the owner is global convexity `Function.IsConvex` of a product function
  `f : U × X → WithBotTop α`; this is the intrinsic level where slicing is defined.
- `bridge/view`: the bifunction form is recovered by taking `f = uncurry F`, so the source
  statement is a direct specialization of the intrinsic product-function slice theorem.

Domain-style sampling used here:
- `Function.IsConvex` from `ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2`;
- `Function.IsConvex.convex_epigraph` from the same file as the owner-level epigraph bridge;
- `uncurry` only as the source-facing bridge back to bifunction notation.

Primitive data vs derived API:
- primitive data: a product function `f : U × X → WithBotTop α`;
- primitive owner hypothesis: `f.IsConvex 𝕜`;
- derived conclusion: convexity of every fixed-first-coordinate slice
  `(fun x ↦ f (u, x)).IsConvex 𝕜`.

Layer target: `bridge/view`, with the theorem surface at the intrinsic owner level and bifunction
phrasing treated as a direct specialization.
-/

namespace Function.IsConvex

/-- Proposition 6.29.1, intrinsic owner form: if `f : U × X → [-∞,+∞]` is convex, then every
slice obtained by fixing the first coordinate is convex. -/
-- Proof sketch: fix `u : U`. Apply convexity of `f` to the two epigraph points
-- `((u, x₁), r₁)` and `((u, x₂), r₂)`. Since `u` is preserved by convex combinations in the
-- module `U`, the resulting epigraph point is exactly the one for the slice `x ↦ f (u, x)`.
theorem slice
    {f : U × X → WithBotTop α} (hf : f.IsConvex 𝕜) :
    ∀ u : U, (fun x ↦ f (u, x)).IsConvex 𝕜 := by
  intro u
  rw [isConvex_iff_convex_epigraph]
  let S : Set ((U × X) × α) := {r | f r.1 ≤ r.2}
  have hS : Convex 𝕜 S := by
    simpa [S] using hf.convex_epigraph
  intro p hp q hq a b ha hb hab
  have hp' : (((u, p.1), p.2) : (U × X) × α) ∈ S := by
    simpa [S] using hp
  have hq' : (((u, q.1), q.2) : (U × X) × α) ∈ S := by
    simpa [S] using hq
  simpa [S, Prod.smul_mk, Prod.mk_add_mk, ← add_smul, hab] using
    hS hp' hq' ha hb hab

/-- Proposition 6.29.1, source-facing bridge form: if the graph function `uncurry F` is
convex, then each slice `F u` is convex. -/
theorem slice_uncurry
    {F : U → X → WithBotTop α} (hF : (uncurry F).IsConvex 𝕜) :
    ∀ u : U, (F u).IsConvex 𝕜 := by
  intro u
  simpa [uncurry] using hF.slice u

end Function.IsConvex

end

/-! ### Theorem_6_29_1 (from Chap06) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.29.1 has three atomic clauses about a convex bifunction `F`: the
  perturbation function `inf F`, together with the Kuhn--Tucker vector characterization for the
  associated generalized convex program. The domain equality is reused below as an unlabeled
  companion recall.
- `core/canonical`: the existing owner layer is already present as
  `Bifunction.perturbationFunction`, `Bifunction.dom`, and `Bifunction.IsKuhnTuckerVector`.
- `bridge/view`: convexity of `inf F` is the partial-infimum theorem applied to `uncurry F`; the
  effective-domain clause is exactly the existing theorem
  `Bifunction.dom_perturbationFunction_eq_dom`; the Kuhn--Tucker characterization is the
  source-facing sign-correct translation of the Chapter 23 subdifferential owner at `u = 0`.

Domain-style sampling used here:
- `IsConvex.partialInfimum` from `Chap01.Text_5_7_2`;
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.dom_perturbationFunction_eq_dom` from `Definition_6_29_8`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `_root_.subdifferentialAt` / `∂[Y]f(x)` from `Chap05.Definition_23_0_6`.

Layer target:
- clause `(1)` is a thin source-facing theorem on the canonical perturbation-function owner;
- the domain equality is exact-interface reuse of an existing owner theorem, so it is recalled
  directly as an unlabeled companion;
- clause `(2)` is a source-facing bridge from the Kuhn--Tucker owner to the Chapter 23
  subdifferential owner.
-/

section Convexity

variable {𝕜 : Type w} {U : Type u} {X : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]

-- Proof sketch: `perturbationFunction F` is `partialInfimum (uncurry F)`.
-- Apply the canonical partial-infimum convexity theorem to the convex graph function
-- `uncurry F` and rewrite through the owner definition of `perturbationFunction`.
/-- Theorem 6.29.1 (1): if the graph function `uncurry F` is convex, then the
perturbation function `perturbationFunction F` is convex on the perturbation space. -/
theorem perturbationFunction_isConvex
    {F : U → X → WithBotTop 𝕜} (hF : (uncurry F).IsConvex 𝕜) :
    (perturbationFunction F).IsConvex 𝕜 := sorry

end Convexity

section Domain

variable {U : Type u} {X : Type v} {β : Type w}
variable [CompleteLattice β]

/- Companion recall: the effective domain of the perturbation function is exactly the
source-facing bifunction domain `dom F`, already owned by
`Bifunction.dom_perturbationFunction_eq_dom`. -/
recall dom_perturbationFunction_eq_dom

end Domain

section KuhnTucker

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type (max u w)}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "p" => perturbationFunction F

-- Proof sketch: if `uStar` is Kuhn--Tucker, rewrite `optimalValue F` as `p 0` and use the
-- defining inequality `optimalValue F ≤ p u + ⟪u, uStar⟫ₚ` to obtain
-- `p u ≥ p 0 + ⟪u, -uStar⟫ₚ`, hence `-uStar ∈ ∂[UStar]p(0)`. Conversely, if
-- `-uStar ∈ ∂[UStar]p(0)`, the subgradient inequality yields
-- `p 0 ≤ p u + ⟪u, uStar⟫ₚ` for every `u`, while equality at `u = 0` forces the defining
-- shifted infimum to equal `p 0 = optimalValue F`; the hypothesis that `optimalValue F` is
-- finite supplies the two-sided finiteness fields of `IsKuhnTuckerVector`.
/-- Theorem 6.29.1 (2): when the optimal value is finite, a dual vector `u⋆` is a Kuhn--Tucker
vector for `F` exactly when `-u⋆` is a subgradient of the perturbation function at `0`. -/
theorem
    isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) (uStar : UStar) :
    IsKuhnTuckerVector F uStar ↔ -uStar ∈ (∂[UStar]p(0)) := sorry

end KuhnTucker

end Bifunction

/-! ### Corollary_6_29_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.2 says that for a convex bifunction `F`, once the optimal value
  of the associated generalized convex program is finite, failure of Kuhn--Tucker vectors is
  equivalent to the existence of a direction along which the two-sided directional derivative of
  `inf F` at `0` exists and equals `-∞`.
- `core/canonical`: the existing owners are `perturbationFunction F` for `inf F`,
  `kuhnTuckerVectorSet F` (notation `KT(F)`) for Kuhn--Tucker vectors, and
  `Function.HasBilateralDirectionalDerivativeAt` for the two-sided directional derivative.
- `bridge/view`: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of subgradients of
  `perturbationFunction F` at `0`, while Theorem 23.3 identifies emptiness of the subdifferential
  of a finite convex function with existence of a bilateral directional derivative equal to `⊥`.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` and `Bifunction.optimalValue`;
- `Bifunction.perturbationFunction_isConvex` and
  `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite`;
- `Function.HasBilateralDirectionalDerivativeAt`;
- `Function.exists_hasBilateralDirectionalDerivativeAt_eq_bot_of_subdifferentialAt_eq_empty`.

Layer target:
- `source-facing`, stated directly on the canonical bifunction and bilateral-directional-derivative
  owners without adding a separate program wrapper or a limit-expression surrogate.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type z}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [Neg UStar] [HasPairing U UStar 𝕜] [HasPairingNegRight U UStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: Theorem 6.29.1 identifies Kuhn--Tucker vectors with negatives of the
-- subgradients of `perturbationFunction F` at `0`, so nonexistence of Kuhn--Tucker vectors is
-- equivalent to emptiness of that subdifferential. The finiteness hypothesis rewrites as
-- finiteness of `perturbationFunction F` at `0`, and Theorem 23.3 then turns empty
-- subdifferential for the convex function `perturbationFunction F` into the existence of a
-- direction with bilateral directional derivative `⊥`.
/-- Corollary 6.29.2: if `F` is a convex bifunction and the optimal value of the associated
generalized convex program is finite, then the canonical Kuhn--Tucker set `KT(F)` is empty if and
only if there exists a direction `u` for which the two-sided directional derivative of
`perturbationFunction F` at `0` exists and equals `-∞`, expressed by the canonical owner
`Function.HasBilateralDirectionalDerivativeAt (perturbationFunction F) 0 u ⊥`. -/
theorem not_exists_isKuhnTuckerVector_iff_exists_hasBilateralDirectionalDerivativeAt_perturbationFunction_zero_eq_bot
    (hF_convex : convᵇ[𝕜](F))
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (¬ (KT(F) : Set UStar).Nonempty) ↔
      ∃ u : U,
        Function.HasBilateralDirectionalDerivativeAt (perturbationFunction F) (0 : U) u ⊥ := sorry

end

end Bifunction

/-! ### Definition_6_29_2 (from Chap06) -/
universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.2 names the graph function of a bifunction `F : U → X → α`.
- `core/canonical`: this is exactly the pre-existing owner `Function.uncurry F`.
- `bridge/view`: no extra bifunction owner or wrapper theorem is needed; use the canonical
  `Function` API directly.

Domain-style sampling used here:
- `Function.uncurry`;
- `Function.uncurry_apply_pair`;
- `Function.curry`;
- `Function.curry_uncurry`;
- `Function.uncurry_curry`.

Layer target: `core/canonical recall/use`.
-/

/- Definition 6.29.2: the graph function of a bifunction is exactly the canonical uncurried map
`Function.uncurry`. -/
#check (Function.uncurry : (U → X → α) → U × X → α)
#check (Function.uncurry_apply_pair : ∀ (F : U → X → α) (u : U) (x : X),
  Function.uncurry F (u, x) = F u x)
#check (Function.curry : (U × X → α) → U → X → α)
#check (Function.curry_uncurry : ∀ F : U → X → α, Function.curry (Function.uncurry F) = F)
#check (Function.uncurry_curry : ∀ f : U × X → α, Function.uncurry (Function.curry f) = f)

end

end Bifunction

/-! ### Lemma_6_29_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [Preorder α] [AddZeroClass α]

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.2 identifies the parameter domain of the bifunction
  `F u x = f₀ x + δ[α](x | S u)` with the set of parameters whose slice `S u` meets
  `dom(f₀)`.
- `core/canonical`: the existing owner layer already provides the indicator `δ[α](· | C)`, the
  one-variable effective-domain owner `dom(f₀)`, and the bifunction-domain owner `dom F`.
- `bridge/view`: this file should therefore state the result directly as a bridge from
  `dom F` to the intersection description, rather than reintroducing the raw set
  `{u | ∃ x, F u x < ⊤}` as a parallel public owner.

Domain-style sampling used here:
- `dom F` and `mem_dom_iff_exists` from `Definition_6_29_8`;
- `indicator_of_mem`, `indicator_of_notMem`, and `mem_effectiveDomain` from Chapter 1;
- `WithBotTop.add_top_of_ne_bot` from the canonical additive layer.

Primitive data vs derived API:
- primitive data: the slice family `S`, the extended-valued branch `f₀`, and the pointwise
  no-`⊥` hypothesis outside each slice `x ∉ S u → f₀ x ≠ ⊥` required by the
  `WithBotTop` additive semantics;
- derived API: the source intersection formula for the bifunction-domain owner.

Layer target: `bridge/view`.
-/

-- Proof sketch: use the canonical owner test `mem_dom_iff_exists`. If
-- `f₀ x + δ[α](x | S u) < ⊤`, then `x` must belong to `S u`; otherwise the indicator contributes
-- `⊤`, and the no-`⊥` hypothesis forces the sum to be `⊤`. On `S u`, the indicator vanishes, so
-- the same inequality is exactly `f₀ x < ⊤`, i.e. `x ∈ dom(f₀)`.
/-- Lemma 6.29.2: if the objective branch `f₀` never takes `⊥` outside the active slice `S u`,
then the bifunction domain of `u ↦ f₀ + δ[α](· | S u)` is exactly the set of parameters whose
slice set `S u` meets the effective domain `dom(f₀)`. This is the source formula
`dom F = {u | S_u ∩ C ≠ ∅}` with `C = dom f₀`, expressed on the canonical bifunction-domain
owner. -/
theorem dom_add_indicator_eq_setOf_inter_dom_nonempty
    (f₀ : X → WithBotTop α) (S : U → Set X)
    (hf₀_ne_bot : ∀ ⦃u x⦄, x ∉ S u → f₀ x ≠ ⊥) :
    dom ((fun _ : U ↦ f₀) + δᵇ[α](S)) =
      {u | (S u ∩ dom(f₀)).Nonempty} := by
  ext u
  rw [mem_dom_iff_exists]
  constructor
  · rintro ⟨x, hx⟩
    change f₀ x + δ[α](x | S u) < ⊤ at hx
    by_cases hxS : x ∈ S u
    · refine ⟨x, hxS, ?_⟩
      rw [indicator_of_mem (S u) hxS, add_zero] at hx
      rw [mem_effectiveDomain]
      exact hx
    · have hsum : f₀ x + δ[α](x | S u) = ⊤ := by
        rw [indicator_of_notMem (S u) hxS]
        exact WithBotTop.add_top_of_ne_bot (hf₀_ne_bot hxS)
      exact False.elim ((ne_of_lt hx) hsum)
  · rintro ⟨x, hxS, hxdom⟩
    refine ⟨x, ?_⟩
    change f₀ x + δ[α](x | S u) < ⊤
    rw [mem_effectiveDomain] at hxdom
    rw [indicator_of_mem (S u) hxS, add_zero]
    exact hxdom

end

end Bifunction

/-! ### Proposition_6_29_2 (from Chap06) -/
universe u v w z

namespace Bifunction

open Function

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: this item identifies the bifunction domain `dom F` with
  the first-coordinate projection of the graph domain and then records the resulting convexity
  statement for convex bifunctions.
- `core/canonical`: the already-built owners available here are the Chapter 6 bifunction-domain
  owner `dom F` from Definition 6.29.8 and the Chapter 1 graph-domain notation
  `dom(uncurry F)` from Definition 6.29.7.
- `bridge/view`: the proposition is the direct owner bridge from `dom F` to the
  canonical graph-domain image.

Domain-style sampling used here:
- `dom(uncurry F)`;
- convexity of the graph-domain owner `dom(uncurry F)`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β` into a codomain carrying `⊤` and `<`;
- source-facing owner available in this file: `dom F`;
- canonical owner available in this file: `dom(uncurry F)`.

Layer target: `bridge/view`, stated directly in the source-facing set language while reusing the
canonical graph-domain owner.
-/

/-- Membership in the bifunction domain is equivalent to the existence of a graph-domain point of
`uncurry F` above the same parameter. -/
@[simp] theorem mem_dom_iff_exists_mem_dom_uncurry
    {F : U → X → β} {u : U} :
    u ∈ dom F ↔ ∃ x : X, (u, x) ∈ dom(uncurry F) := by
  rw [mem_dom]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [uncurry] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [uncurry] using hx⟩

/-- Proposition 6.29.2: the set of parameters admitting a finite slice value is the
first-coordinate projection of the graph domain of the bifunction. -/
theorem dom_eq_image_fst_dom_uncurry (F : U → X → β) :
    dom F = Prod.fst '' dom(uncurry F) := by
  ext u
  constructor
  · intro hu
    rcases (mem_dom_iff_exists_mem_dom_uncurry (F := F) (u := u)).1 hu with ⟨x, hx⟩
    exact ⟨(u, x), hx, rfl⟩
  · rintro ⟨⟨u', x⟩, hx, rfl⟩
    exact (mem_dom_iff_exists_mem_dom_uncurry (F := F) (u := u')).2 ⟨x, hx⟩

end

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {β : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid U] [SMul 𝕜 U]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [Top β] [LT β]

-- Proof sketch: transport convexity from `dom(uncurry F)` to `dom F` across
-- `dom_eq_image_fst_dom_uncurry`.
/-- If the graph-domain owner `dom(uncurry F)` is convex, then the parameter-domain owner
`dom F` is convex. -/
theorem convex_dom {F : U → X → β}
    (hdom_uncurry : Convex 𝕜 (dom(uncurry F))) :
    Convex 𝕜 (dom F) := by
  rw [dom_eq_image_fst_dom_uncurry]
  rw [convex_iff_add_mem]
  rintro _ ⟨⟨u₁, x₁⟩, hx₁, rfl⟩ _ ⟨⟨u₂, x₂⟩, hx₂, rfl⟩ a b ha hb hab
  exact ⟨a • (u₁, x₁) + b • (u₂, x₂), hdom_uncurry hx₁ hx₂ ha hb hab, rfl⟩

end

end Bifunction

/-! ### Theorem_6_29_2 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.29.2 says that a polyhedral convex bifunction has polyhedral
  objective and perturbation functions, and that finite optimal value yields existence and
  polyhedrality of the primal optimal-solution set and the Kuhn--Tucker-vector set.
- `core/canonical`: the existing owner layer is already present as
  `Function.HasPolyhedralEpigraph` on `Function.uncurry F`, `objective`,
  `perturbationFunction`, `optimalValue`, `optimalSolutionSet`, and the intrinsic-dual
  Kuhn--Tucker owner `(kuhnTuckerVectorSet F : Set (StrongDual 𝕜 U))`.
- `bridge/view`: the primal optimal-solution set is compared with `minimumSet (F)₀`, while the
  Kuhn--Tucker vectors are compared with the intrinsic subdifferential set
  `∂[StrongDual 𝕜 U](perturbationFunction F)(0)`.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph.comp_linearMap` and
  `Function.HasPolyhedralEpigraph.linearImage` from Chapter 19;
- `Function.HasPolyhedralEpigraph.isPolyhedral_preimage_Iic` from Chapter 19;
- `objective` from `Definition_6_29_13`;
- `perturbationFunction` and `IsKuhnTuckerVector` from `Theorem_6_29_1`;
- `optimalSolutionSet` and `optimalSolutionSet_eq_minimumSet_of_consistent` from `Lemma_6_29_8`;
- `Function.HasPolyhedralEpigraph.exists_mem_isMinOn_of_isPolyhedral_of_lower_bound` from
  `Corollary_6_27_4`;
- `Function.HasPolyhedralEpigraph.subdifferentialAt_nonempty` and
  `Function.HasPolyhedralEpigraph.subdifferentialAt_isPolyhedral` from `Theorem_23_10`, both
  on `StrongDual 𝕜 U`.

Primitive data vs derived API:
- primitive source data: a bifunction `F`;
- primitive owner hypothesis: `polyᵇ F`;
- derived owners: polyhedrality of `(F)₀` and `perturbationFunction F`, existence of an element of
  `optimalSolutionSet F`, nonemptiness of
  `(kuhnTuckerVectorSet F : Set (StrongDual 𝕜 U))`, and the polyhedrality of the corresponding
  primal and intrinsic-dual solution sets.

Ambient refinement:
- clauses `(1)`, `(2)`, `(3)`, and `(5)` live on the scalar-generic Chapter 19/27 owner layer;
- clauses `(4)` and `(6)` stay on the canonical intrinsic-dual owner `StrongDual 𝕜 U`, matching
  the scalar-generic Chapter 23 subdifferential API.

Layer target: `source-facing`, stated directly on the established Chapter 6 owners and split only
along the genuine owner boundary between scalar-generic polyhedral program data and the intrinsic
strong-dual API.
-/

section Objective

variable {𝕜 : Type w} [Semiring 𝕜] [Preorder 𝕜]
variable {U : Type u} [AddCommMonoid U] [Module 𝕜 U]
variable {X : Type v} [AddCommMonoid X] [Module 𝕜 X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: rewrite `(F)₀` as the pullback of `Function.uncurry F` along the linear map
-- `LinearMap.inr 𝕜 U X : X →ₗ[𝕜] U × X`, then apply the Chapter 19 pullback owner for
-- polyhedral epigraphs.
/-- Theorem 6.29.2 (1): if `F` is a polyhedral convex bifunction, then its objective function
`F₀` is a polyhedral convex function. -/
theorem objective_hasPolyhedralEpigraph
    (hF_poly : polyᵇ F) :
    ((F)₀).HasPolyhedralEpigraph := sorry

end Objective

section Perturbation

variable {𝕜 : Type w} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [DenselyOrdered 𝕜] [NoBotOrder 𝕜] [NoMaxOrder 𝕜]
variable {U : Type u} [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable {X : Type v} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: rewrite `perturbationFunction F` as the linear image in the `U`-direction of the
-- polyhedral graph function `Function.uncurry F`, then apply the Chapter 19 linear-image theorem
-- for polyhedral epigraphs.
/-- Theorem 6.29.2 (2): if `F` is a polyhedral convex bifunction, then its perturbation function
`perturbationFunction F` is a polyhedral convex function. -/
theorem perturbationFunction_hasPolyhedralEpigraph
    (hF_poly : polyᵇ F) :
    (perturbationFunction F).HasPolyhedralEpigraph := sorry

end Perturbation

section PolyhedralProgram

variable {𝕜 : Type w} [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] [CompleteSpace 𝕜]
variable {U : Type u} [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable {X : Type v} [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: clause `(1)` gives a polyhedral objective. The finite optimal value furnishes a
-- scalar lower bound for `(F)₀`, so Chapter 6.27 attainment on the polyhedral set `Set.univ`
-- yields a minimizer of `(F)₀`. Consistency follows from the finite-value hypothesis, and
-- Lemma 6.29.8 then identifies that minimizer with an element of `optimalSolutionSet F`.
/-- Theorem 6.29.2 (3): if `F` is polyhedral and `optimalValue F` is finite, then the generalized
convex program attached to `F` has an optimal solution. -/
theorem optimalSolutionSet_nonempty_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (optimalSolutionSet F).Nonempty := sorry

-- Proof sketch: clause `(1)` gives a polyhedral objective. Under finite optimal value,
-- `optimalSolutionSet F` agrees with `minimumSet (F)₀`, which is the scalar sublevel set of
-- `(F)₀` at the finite level `optimalValue F`. Chapter 19 makes that scalar sublevel set
-- polyhedral.
/-- Theorem 6.29.2 (5): if `F` is polyhedral and `optimalValue F` is finite, then the set of all
optimal solutions is a polyhedral convex set. -/
theorem optimalSolutionSet_isPolyhedral_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (optimalSolutionSet F).IsPolyhedral 𝕜 := sorry

end PolyhedralProgram

section CanonicalDual

variable {𝕜 : Type w} [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {U : Type u} {X : Type v}
variable [SeminormedAddCommGroup U] [NormedSpace 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]

variable {F : U → X → WithBotTop 𝕜}

-- Proof sketch: clause `(2)` gives a polyhedral perturbation function. The finiteness of
-- `optimalValue F = perturbationFunction F 0` makes the value at `0` finite, so Theorem 23.10
-- gives a nonempty intrinsic subdifferential at `0` in `StrongDual 𝕜 U`. Theorem 6.29.1 then
-- identifies Kuhn--Tucker vectors with the negatives of those subgradients.
/-- Theorem 6.29.2 (4): if `F` is polyhedral and `optimalValue F` is finite, then the generalized
convex program attached to `F` has a Kuhn--Tucker vector in the canonical dual
`StrongDual 𝕜 U`. -/
theorem kuhnTuckerVectorSet_nonempty_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (KT(F) : Set (StrongDual 𝕜 U)).Nonempty := sorry

-- Proof sketch: clause `(2)` gives a polyhedral perturbation function, and the finiteness
-- hypothesis gives a finite value at `0`. Theorem 23.10 makes the intrinsic subdifferential
-- `∂[StrongDual 𝕜 U](perturbationFunction F)(0)` nonempty and polyhedral, while Theorem 6.29.1
-- identifies `KT(F)` with its image under negation.
/-- Theorem 6.29.2 (6): if `F` is polyhedral and `optimalValue F` is finite, then the set of all
Kuhn--Tucker vectors in the canonical dual `StrongDual 𝕜 U` is a polyhedral convex set. -/
theorem kuhnTuckerVectorSet_isPolyhedral_of_optimalValue_finite
    (hF_poly : polyᵇ F)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop 𝕜) ⊤) :
    (KT(F) : Set (StrongDual 𝕜 U)).IsPolyhedral 𝕜 := sorry

end CanonicalDual

end Bifunction

/-! ### Corollary_6_29_3 (from Chap06) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar
open Function

set_option linter.style.longLine false

universe u v

namespace Bifunction

section

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : E → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set (StrongDual ℝ E))

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 6.29.3 characterizes uniqueness of the Kuhn--Tucker object for the
  generalized convex program attached to a convex bifunction `F` by differentiability of the
  perturbation function `p = perturbationFunction F` at `0`. In the inner-product bridge
  specialization, the unique Kuhn--Tucker vector is `-∇ p.realBranch 0`, and only after that
  Euclidean bridge does one read its coordinates by partial derivatives.
- `core/canonical`: the existing owners are `Bifunction.perturbationFunction`,
  `Bifunction.IsKuhnTuckerVector`, the Chapter 23 subdifferential owner at `0`, and the Chapter
  25 differentiability/gradient owners for finite real-valued functions on the perturbation
  space.
- `bridge/view`: Theorem 6.29.1 identifies Kuhn--Tucker functionals with negative subgradients of
  the perturbation function `p` at `0`. Definition 6.29.10 supplies the missing local-finiteness
  owner `IsStrictlyConsistent F ↔ 0 ∈ interior (dom p)`, Theorem 25.2 turns uniqueness of that
  subgradient into differentiability of `p.realBranch`, the Fréchet-Riesz inner-product bridge
  turns the unique supporting functional into the vector `-∇ p.realBranch 0`, and
  Theorem 25.1.3 is only the final coordinate translation on the Euclidean perturbation space
  `E = EuclideanSpace ℝ ι`.

Primary mathematical domain:
- perturbation functions of convex bifunctions, Kuhn--Tucker functionals/vectors, and the
  real differentiability/subgradient bridge (with finite-dimensionality needed only for the
  uniqueness-equivalence direction).

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from `Definition_6_29_1`;
- `Bifunction.IsKuhnTuckerVector` from `Definition_6_29_19`;
- `Bifunction.isKuhnTuckerVector_iff_neg_mem_subdifferentialAt_zero_of_optimalValue_finite` from
  `Theorem_6_29_1`;
- `Function.differentiableAt_iff_existsUnique_mem_subdifferentialAt` from `Theorem_25_2`;
- `∇` on real inner-product spaces from mathlib's gradient owner;
- `Function.gradient_eq_partialDeriv` from `Theorem_25_1_3`;
- the canonical finite real branch `Function.realBranch p` of the perturbation function.

Primitive data vs derived API:
- primitive source data: a convex bifunction `F`, finiteness of `optimalValue F`, and the local
  finiteness owner `IsStrictlyConsistent F`;
- primitive owner surface: `perturbationFunction F` and `IsKuhnTuckerVector F` on the intrinsic
  dual owner `StrongDual ℝ E`;
- derived API in this file: the intrinsic uniqueness criterion via strict consistency together
  with differentiability of `p.realBranch` at `0`, the inner-product bridge
  `uStar = -∇ p.realBranch 0`, and the final Euclidean coordinate formula on the perturbation
  variable via the Chapter 25 partial-derivative owner.

Layer target:
- the first theorem is `source-facing`, but on the weakest finite-dimensional real normed-space
  owner layer `StrongDual ℝ E`;
- the vector identity is `bridge/view` on the inner-product specialization;
- the coordinate formula is the downstream Euclidean bridge only, so only the perturbation space
  should be specialized to Euclidean coordinates.
-/

-- Proof sketch: apply Theorem 6.29.1 to identify Kuhn--Tucker vectors with negative
-- subgradients of `p` at `0`. Definition 6.29.10 records the source's local finiteness at the
-- base point as `IsStrictlyConsistent F`, and once that interior-domain hypothesis is present,
-- uniqueness of the subgradient is equivalent to differentiability of `p.realBranch` at `0` by
-- the Chapter 25 singleton-subdifferential criterion for convex functions.
/-- Corollary 6.29.3 on the intrinsic dual owner: for a convex bifunction `F`, if the optimal
value of the associated generalized convex program is finite, then the program has a unique
Kuhn--Tucker functional exactly when the program is strictly consistent and the real branch
`p.realBranch` of the perturbation function is differentiable at `0`. -/
theorem
    existsUnique_kuhnTuckerFunctional_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    (∃! uStar : StrongDual ℝ E, uStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := sorry

end

section

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : E → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set E)

-- Proof sketch: unpack `hkt : uStar ∈ KT(F)` to recover finite optimal value, then invoke
-- Theorem 6.29.1 to identify the Kuhn--Tucker vector with a negative subgradient of `p` at `0`.
-- The missing local-finiteness hypothesis is the canonical owner `IsStrictlyConsistent F`; with
-- that in place, differentiability of `p.realBranch` rewrites the unique subgradient as
-- `∇ p.realBranch 0`, yielding the source-facing vector identity.
/-- Inner-product bridge for Corollary 6.29.3: in the differentiable case, any Kuhn--Tucker
vector is exactly the negative gradient `-∇ p.realBranch 0`, provided the generalized convex
program is strictly consistent; finiteness of the optimal value is derived from the Kuhn--Tucker
hypothesis. -/
theorem kuhnTuckerVector_eq_neg_gradient_perturbationFunction_zero
    (hF : (uncurry F).IsConvex ℝ)
    (hstrict : IsStrictlyConsistent F)
    {uStar : E}
    (hkt : uStar ∈ KT(F))
    (hdiff : DifferentiableAt ℝ p.realBranch 0) :
    uStar = -∇ p.realBranch 0 := sorry

end

section

variable {E : Type u} {X : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : E → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set E)

-- Proof sketch: transfer the intrinsic dual-owner theorem to the Riesz-identified vector model
-- `E`, leaving the theorem surface on the chapter notation `KT(F)`.
/-- Corollary 6.29.3 in the inner-product vector model: if the optimal value is finite, then
there is a unique Kuhn--Tucker vector exactly when the program is strictly consistent and
`p.realBranch` is differentiable at `0`. -/
theorem
    existsUnique_kuhnTuckerVector_iff_differentiableAt_perturbationFunction_zero_of_optimalValue_finite
    (hF : (uncurry F).IsConvex ℝ)
    (hoptimal : optimalValue F ∈ Set.Ioo (⊥ : WithBotTop ℝ) ⊤) :
    (∃! uStar : E, uStar ∈ KT(F)) ↔
      IsStrictlyConsistent F ∧ DifferentiableAt ℝ p.realBranch 0 := sorry

end

section

variable {ι : Type u} {X : Type v}
variable [Fintype ι]
variable [AddCommMonoid X] [Module ℝ X]

variable {F : EuclideanSpace ℝ ι → X → WithBotTop ℝ}

local notation "p" => perturbationFunction F
local notation "p.realBranch" => Function.realBranch p
local notation "KT(" F ")" => (kuhnTuckerVectorSet F : Set (EuclideanSpace ℝ ι))

-- Proof sketch: first rewrite `uStar` as `-∇ p.realBranch 0` by the inner-product bridge above;
-- strict consistency supplies the missing local finiteness at `0`, and the needed optimal-value
-- finiteness input is derived by unpacking `hkt : uStar ∈ KT(F)`. Then read the `i`-th coordinate
-- of the gradient using Theorem 25.1.3.
/-- In the differentiable case, every Kuhn--Tucker vector has coordinates given by the negative
partial derivatives of the perturbation function at `0`. This is the Euclidean coordinate bridge
of the canonical vector identity `uStar = -∇ p.realBranch 0`, and only the perturbation space is
specialized to Euclidean coordinates here; strict consistency supplies the source's local
finiteness hypothesis, while finiteness of the optimal value is derived from the Kuhn--Tucker
hypothesis. -/
theorem
    kuhnTuckerVector_apply_eq_neg_partialDeriv_perturbationFunction_zero
    (hF : (uncurry F).IsConvex ℝ)
    (hstrict : IsStrictlyConsistent F)
    {uStar : EuclideanSpace ℝ ι}
    (hkt : uStar ∈ KT(F))
    (hdiff : DifferentiableAt ℝ p.realBranch 0)
    (i : ι) :
    uStar i = -partialDeriv p.realBranch 0 i := sorry

end

end Bifunction

/-! ### Definition_6_29_3 (from Chap06) -/
noncomputable section

universe u v w

/-- Source notation for the indicator bifunction attached to a set-valued map, with codomain
inferred from context. -/
scoped[Rockafellar] notation:70 "δᵇ(" S ")" =>
  (fun u ↦ Set.indicator (S u)ᶜ (fun _ ↦ (⊤ : WithBotTop _)))

/-- Source notation for the indicator bifunction attached to a set-valued map. -/
scoped[Rockafellar] notation:70 "δᵇ[" β "](" S ")" =>
  (fun u ↦ Set.indicator (S u)ᶜ (fun _ ↦ (⊤ : WithBotTop β)))

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [Zero α]
variable (S : U → Set X)

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.29.3 introduces the `(+∞)` indicator bifunction attached to the
  family of feasible slices `u ↦ S u`.
- `core/canonical`: the Chapter 1 set indicator `δ[α](x | C)` already owns the primitive
  `0/+∞` branch data on each slice, so no second bifunction owner is needed here.
- `bridge/view`: after fixing `u`, all slice formulas and `0`/`⊤` branch lemmas are immediate
  instances of the Chapter 1 indicator API.

Primary mathematical domain:
- slice-wise indicator functions of set-valued maps.

Domain-style sampling used here:
- `indicator`;
- `indicator_def`;
- `indicator_of_mem`;
- `indicator_of_notMem`.

Primitive data vs derived API:
- primitive data: only the family of sets `S : U → Set X`;
- derived API: evaluation at `(u, x)` and the branch lemmas, all inherited from the Chapter 1
  indicator after specializing to the slice `S u`.

Layer target: `source-facing`, by direct reuse of the Chapter 1 owner rather than a parallel local
wrapper.
-/

@[simp] theorem indicatorBifunction_apply (u : U) (x : X) :
    (δᵇ[α](S)) u x = δ[α](x | S u) :=
  rfl

@[simp] theorem indicatorBifunction_of_mem (u : U) {x : X} (hx : x ∈ S u) :
    (δᵇ[α](S)) u x = 0 := by
  simpa [indicatorBifunction_apply] using
    (indicator_of_mem (α := α) (C := S u) hx)

@[simp] theorem indicatorBifunction_of_notMem (u : U) {x : X} (hx : x ∉ S u) :
    (δᵇ[α](S)) u x = ⊤ := by
  simpa [indicatorBifunction_apply] using
    (indicator_of_notMem (α := α) (C := S u) hx)

/- Definition 6.29.3: the indicator bifunction of a set-valued map `S` is the slice-wise Chapter 1
indicator. The canonical owner remains the set-indicator notation on each slice; this file uses
the direct source notation `δᵇ[α](S)` for that curried view. -/
#check (δᵇ(S) : U → X → WithBotTop α)
#check (δᵇ[α](S) : U → X → WithBotTop α)

end

end Bifunction

/-! ### Lemma_6_29_3 (from Chap06) -/
noncomputable section

universe u v w x

namespace OrdinaryConvexProgram

section

open scoped Rockafellar

variable {𝕜 : Type x} {E : Type u} {β : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

/-!
Source/core/bridge triage:

- `source-facing`: Lemma 6.29.3 says that every point of the source constraint set `C`
  determines a perturbation parameter lying in the parameter domain `dom F`.
- `core/canonical`: the owner parameter space is `P.ConstraintIndex → β`, and the associated
  bifunction-domain owner is already `dom P.perturbedProblem`.
- `bridge/view`: the source tuple `(f₁(x), …, f_m(x))` is represented intrinsically as the
  ambient constraint-family value `fun i ↦ P.constraint i x`, where `x : E` is paired with
  a membership witness `hxC : x ∈ P.constraintSet`.

Domain-style sampling used here:
- `OrdinaryConvexProgram` and `P.ConstraintIndex` from `Definition_6_28_2`;
- `OrdinaryConvexProgram.perturbedProblem` from `Definition_6_28_4`;
- `Bifunction.dom` and `Bifunction.mem_dom` from `Definition_6_29_8`.

Primitive data vs derived API:
- primitive source data: the program `P`, an ambient point `x : E`, and a witness
  `hxC : x ∈ P.constraintSet`;
- canonical owner-side target: membership of the corresponding constraint-value parameter in
  `dom P.perturbedProblem`;
- derived corollary: nonemptiness of that parameter domain as soon as `P.constraintSet` is
  nonempty.

Layer target: `source-facing`, on the existing owner `P.perturbedProblem`.
-/

-- Proof sketch: for `x : E` with `hxC : x ∈ P.constraintSet`, let `u` be the parameter whose
-- inequality and equality coordinates are the corresponding constraint values at `x`. Then `x`
-- satisfies the perturbed inequalities and equalities defining `P.perturbedFeasibleSet u`, so
-- `P.perturbedProblem u x` is finite. Hence the parameter lies in the canonical bifunction domain
-- `dom P.perturbedProblem`.
/-- Lemma 6.29.3: every point of the constraint set of an ordinary convex program determines a
perturbation parameter lying in the parameter domain of the associated perturbed problem. -/
theorem constraintValueParameter_mem_dom_perturbedProblem
    {x : E} (hxC : x ∈ P.constraintSet) :
    (fun i ↦ P.constraint i x) ∈ dom P.perturbedProblem := by
  let u : P.ConstraintIndex → β := fun i ↦ P.constraint i x
  rw [Bifunction.mem_dom]
  refine ⟨x, ?_⟩
  rw [_root_.mem_effectiveDomain, P.perturbedProblem_apply]
  have hx :
      x ∈ P.perturbedFeasibleSet u := by
    rw [P.mem_perturbedFeasibleSet_split]
    refine ⟨hxC, ?_, ?_⟩
    · intro i
      simp [u, OrdinaryConvexProgram.constraint]
    · intro j
      simp [u, OrdinaryConvexProgram.constraint]
  simpa [u, hx] using (WithBotTop.coe_lt_top (P.objective ⟨x, hxC⟩))

/-- If the constraint set of an ordinary convex program is nonempty, then the parameter domain of
its perturbed problem is nonempty. -/
theorem dom_perturbedProblem_nonempty (hC : P.constraintSet.Nonempty) :
    (dom P.perturbedProblem).Nonempty := by
  rcases hC with ⟨x, hx⟩
  exact ⟨_, P.constraintValueParameter_mem_dom_perturbedProblem hx⟩

end

end OrdinaryConvexProgram

/-! ### Proposition_6_29_3 (from Chap06) -/
universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {β : Type w}
variable [Top β] [Bot β] [LT β]

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 6.29.3 identifies the parameter domain of a convex bifunction
  whose graph is nowhere `⊥` with the set of parameters whose slices are proper convex functions.
- `core/canonical`: the already-built chapter owners available here are the one-variable
  effective-domain notation `dom(·)`, the bifunction-domain owner `dom F`,
  `Function.IsProper` for properness of a codomain-agnostic slice, and the primitive
  pointwise `⊥`-exclusion `f x ≠ ⊥` built into that owner,
  `Function.IsConvex 𝕜` for convexity.
- `bridge/view`: Definition 6.29.8 identifies the parameter domain `dom F` with slice
  effective-domain nonemptiness. The properness part is the genuine new content here, while the
  convexity part comes from restricting graph convexity to a fixed first variable.

Domain-style sampling used here:
- `Bifunction.dom` from `Definition_6_29_8`;
- the notation `dom(·)` and `mem_effectiveDomain` from
  `Chap01.Definition_4_4`, available through `Chap01.Definition_4_6`;
- `Function.IsProper`, `Function.isProper_iff`, and `Function.IsProper.ne_bot` from
  `Chap01.Definition_4_6`;
- `Function.IsConvex 𝕜` from `Chap01.Theorem_4_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → β`;
- primitive owner hypothesis for the properness clause: no-`⊥` on the parameter domain,
  i.e. `∀ ⦃u⦄, u ∈ dom F → ∀ x, F u x ≠ ⊥`;
- derived companion hypothesis: full graph properness
  `(Function.uncurry F).IsProper`, used only to recover that primitive no-`⊥` data;
- derived conclusions: slice properness and slice convexity for each `u`.

Layer target: `source-facing`, stated directly with the existing chapter owners and the defining
owner from Definition 6.29.8 rather than through a new packaged notion of “proper convex slice”.
-/

-- Proof sketch: from `u ∈ dom F`, the hypothesis `hF_ne_bot_on_dom` gives that the whole slice
-- `F u` is nowhere `⊥`, while `u ∈ dom F` itself is exactly nonempty slice effective domain.
-- Hence `F u` is proper. Conversely, if the slice `F u` is proper, then its domain is nonempty,
-- so `u ∈ dom F`.
/-- The parameter domain from Definition 6.29.8 is exactly the set of parameters whose slices are
proper, provided slices over that domain are nowhere `⊥`. -/
theorem dom_eq_setOf_slice_isProper
    {F : U → X → β}
    (hF_ne_bot_on_dom : ∀ ⦃u⦄, u ∈ dom F → ∀ x, F u x ≠ ⊥) :
    dom F = {u : U | (F u).IsProper} := by
  ext u
  constructor
  · intro hu
    exact ⟨mem_dom.mp hu, hF_ne_bot_on_dom hu⟩
  · intro hu
    exact mem_dom.mpr hu.nonempty_dom

/-- Properness-form restatement of `dom_eq_setOf_slice_isProper`. The graph-proper hypothesis is
used only to recover the primitive graphwise no-`⊥` condition. -/
theorem dom_eq_setOf_slice_isProper_of_isProper
    {F : U → X → β}
    (hF_proper : (Function.uncurry F).IsProper) :
    dom F = {u : U | (F u).IsProper} :=
  dom_eq_setOf_slice_isProper (fun {u} _ x ↦ hF_proper.ne_bot (u, x))

end

section

variable {𝕜 : Type z} {U : Type u} {X : Type v} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid X] [SMul 𝕜 X]
variable [AddCommMonoid α] [SMul 𝕜 α] [LE α] [LT α]

-- Proof sketch: the properness part is exactly `dom_eq_setOf_slice_isProper`. The extra convexity
-- requirement on the right is supplied by a primitive slice-wise convexity hypothesis, so the
-- right-hand side reduces to "slice proper and slice convex" without introducing graph-level
-- assumptions.
/-- Core owner form of Proposition 6.29.3: if slices over `dom F` are convex and nowhere `⊥`,
then the parameter domain from Definition 6.29.8 is exactly the set of parameters whose slices are
proper convex functions. -/
theorem dom_eq_setOf_slice_isProperConvex_of_sliceConvex
    {F : U → X → WithBotTop α}
    (hF_slice_convex_on_dom : ∀ ⦃u⦄, u ∈ dom F → (F u).IsConvex 𝕜)
    (hF_ne_bot_on_dom : ∀ ⦃u⦄, u ∈ dom F → ∀ x, F u x ≠ ⊥) :
    dom F = {u : U | (F u).IsProper ∧ (F u).IsConvex 𝕜} := by
  ext u
  rw [dom_eq_setOf_slice_isProper hF_ne_bot_on_dom]
  constructor
  · intro hu
    exact ⟨hu, hF_slice_convex_on_dom hu.nonempty_dom⟩
  · intro hu
    exact hu.1

section

variable [AddCommMonoid U] [Module 𝕜 U]

-- Proof sketch: apply the primitive slice-convex theorem above, using Proposition 6.29.1 to
-- obtain slice convexity from graph convexity of `Function.uncurry F`.
/-- Proposition 6.29.3, source-facing graph form: if a bifunction graph is convex and nowhere
`⊥`, then its parameter domain from Definition 6.29.8 is exactly the set of parameters whose
slices are proper convex functions. -/
theorem dom_eq_setOf_slice_isProperConvex
    {F : U → X → WithBotTop α}
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_ne_bot : ∀ u x, F u x ≠ ⊥) :
    dom F = {u : U | (F u).IsProper ∧ (F u).IsConvex 𝕜} := by
  refine dom_eq_setOf_slice_isProperConvex_of_sliceConvex ?_ ?_
  · intro u _
    exact hF_convex.slice_uncurry u
  · intro u _ x
    exact hF_ne_bot u x

/-- Textbook proper-convex restatement of Proposition 6.29.3. The graph-proper hypothesis adds no
new primitive data beyond the graphwise no-`⊥` condition used by the main theorem. -/
theorem dom_eq_setOf_slice_isProperConvex_of_isProper
    {F : U → X → WithBotTop α}
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_proper : (Function.uncurry F).IsProper) :
    dom F = {u : U | (F u).IsProper ∧ (F u).IsConvex 𝕜} :=
  dom_eq_setOf_slice_isProperConvex hF_convex (fun u x ↦ hF_proper.ne_bot (u, x))

end

end

end Bifunction
