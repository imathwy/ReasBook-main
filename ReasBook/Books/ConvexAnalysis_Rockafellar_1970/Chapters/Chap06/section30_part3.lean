import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_6_30_12 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [ConditionallyCompleteLattice α] [Add α] [Zero U]
variable [HasPairing U UStar (WithBotTop α)]

local notation "shiftedSup(" G ", " uStar ")" =>
  (⨆ u : U, ⟪u, uStar⟫ₚ + upperPerturbationFunction G u)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.12 introduces the notion of a Kuhn--Tucker vector `u⋆` for
  the concave program attached to a bifunction `G`.
- `core/canonical`: the existing Chapter 6 owners are
  `Bifunction.upperPerturbationFunction` from Definition 6.30.11 and the Chapter 12 Fenchel
  owner `convexConjugate` applied to `- upperPerturbationFunction G` once the additive
  order-dual codomain structure is available.
- `bridge/view`: at the present weak codomain generality the source displayed supremum identity is
  kept as the primitive owner-side formulation, while the pointwise inequality
  `⟪u, u⋆⟫ₚ + upperPerturbationFunction G u ≤ upperPerturbationFunction G 0` is the equivalent
  supporting-hyperplane reformulation and a later companion theorem bridges the source supremum
  to the canonical conjugate owner.

Domain-style sampling used here:
- `Bifunction.upperPerturbationFunction` and `upperPerturbationFunction_apply` from
  Definition 6.30.11;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- `Bifunction.IsKuhnTuckerVector` from Definition 6.29.19 as the infimum-side owner pattern;
- `Bifunction.IsDualKuhnTuckerVector` from Definition 6.30.17 as the dual supremum-side owner
  pattern.

Primitive data vs derived API:
- primitive source data: the bifunction `G` and the dual vector `u⋆`;
- primitive owner in this file: `Bifunction.IsConcaveKuhnTuckerVector G uStar`, defined by the
  interval-membership finiteness and equality statement for the shifted supremum over
  perturbations;
- derived API: bundled finiteness, the supporting-hyperplane inequality, finiteness of the dual
  value `upperPerturbationFunction G 0`, and the bridge to the Fenchel conjugate owner.

Layer target: `source-facing`. This item introduces a genuine new property of dual vectors for a
concave program, so it is exposed directly on the existing bifunction owner rather than through a
witness package or a restated conjugate wrapper.
-/

/-- Definition 6.30.12: a vector `u⋆` is a Kuhn--Tucker vector for the concave program attached
to `G` when the supremum of the shifted perturbation values
`⟪u, u⋆⟫ₚ + upperPerturbationFunction G u` is finite and equals the unperturbed optimal value
`upperPerturbationFunction G 0`. This is the source-facing owner for the Chapter 6 concave
program, with the canonical conjugate view deferred to companion theorems. -/
class IsConcaveKuhnTuckerVector (G : U → X → WithBotTop α) (uStar : UStar) : Prop where
  supremum_mem_Ioo : shiftedSup(G, uStar) ∈ Set.Ioo (⊥ : WithBotTop α) ⊤
  supremum_eq_upperPerturbationFunction_zero :
    shiftedSup(G, uStar) = upperPerturbationFunction G 0

namespace IsConcaveKuhnTuckerVector

variable {G : U → X → WithBotTop α} {uStar : UStar}

/-- Lower finiteness bound from the defining interval-membership field. -/
theorem supremum_bot_lt (h : IsConcaveKuhnTuckerVector G uStar) :
    ⊥ < shiftedSup(G, uStar) :=
  h.supremum_mem_Ioo.1

/-- Upper finiteness bound from the defining interval-membership field. -/
theorem supremum_lt_top (h : IsConcaveKuhnTuckerVector G uStar) :
    shiftedSup(G, uStar) < ⊤ :=
  h.supremum_mem_Ioo.2

-- Proof sketch: unpack the defining interval-membership field `supremum_mem_Ioo`.
/-- A concave Kuhn--Tucker vector makes the defining shifted perturbation supremum finite. -/
theorem supremum_finite (h : IsConcaveKuhnTuckerVector G uStar) :
    ⊥ < shiftedSup(G, uStar) ∧ shiftedSup(G, uStar) < ⊤ :=
  ⟨h.supremum_bot_lt, h.supremum_lt_top⟩

-- Proof sketch: take the symmetric form of the defining equality
-- `h.supremum_eq_upperPerturbationFunction_zero`.
/-- A concave Kuhn--Tucker vector rewrites the unperturbed upper perturbation value as the
defining shifted supremum. -/
theorem upperPerturbationFunction_zero_eq_supremum
    (h : IsConcaveKuhnTuckerVector G uStar) :
    upperPerturbationFunction G 0 = shiftedSup(G, uStar) :=
  h.supremum_eq_upperPerturbationFunction_zero.symm

-- Proof sketch: rewrite `upperPerturbationFunction G 0` using
-- `upperPerturbationFunction_zero_eq_supremum`; then every term of the indexed supremum is below
-- the supremum itself.
/-- A concave Kuhn--Tucker vector satisfies the supporting-hyperplane inequality
`⟪u, u⋆⟫ₚ + upperPerturbationFunction G u ≤ upperPerturbationFunction G 0` for every
perturbation `u`. -/
theorem pairing_add_upperPerturbationFunction_le_upperPerturbationFunction_zero
    (h : IsConcaveKuhnTuckerVector G uStar) (u : U) :
    ⟪u, uStar⟫ₚ + upperPerturbationFunction G u ≤ upperPerturbationFunction G 0 := by
  rw [h.upperPerturbationFunction_zero_eq_supremum]
  exact le_iSup (fun u : U ↦ ⟪u, uStar⟫ₚ + upperPerturbationFunction G u) u

-- Proof sketch: rewrite `upperPerturbationFunction G 0` using
-- `upperPerturbationFunction_zero_eq_supremum`, then transfer the lower and upper bounds from
-- `supremum_mem_Ioo`.
/-- A concave Kuhn--Tucker vector forces the unperturbed upper perturbation value to lie in the
finite interval `Set.Ioo (⊥ : WithBotTop α) ⊤`. -/
theorem upperPerturbationFunction_zero_mem_Ioo
    (h : IsConcaveKuhnTuckerVector G uStar) :
    upperPerturbationFunction G 0 ∈ Set.Ioo (⊥ : WithBotTop α) ⊤ := by
  rw [h.upperPerturbationFunction_zero_eq_supremum]
  exact h.supremum_mem_Ioo

-- Proof sketch: rewrite `upperPerturbationFunction G 0` using
-- `upperPerturbationFunction_zero_eq_supremum`, then transfer the lower and upper bounds from
-- `supremum_mem_Ioo`.
/-- A concave Kuhn--Tucker vector forces the unperturbed upper perturbation value to be finite. -/
theorem upperPerturbationFunction_zero_finite
    (h : IsConcaveKuhnTuckerVector G uStar) :
    ⊥ < upperPerturbationFunction G 0 ∧ upperPerturbationFunction G 0 < ⊤ := by
  exact h.upperPerturbationFunction_zero_mem_Ioo

end IsConcaveKuhnTuckerVector

end

section

variable {U : Type u} {X : Type v} {UStar : Type z} {α : Type w}
variable [Add α] [InvolutiveNeg α] [ConditionallyCompleteLattice α]
variable [HasPairing U UStar (WithBotTop α)]

local notation "shiftedSup(" G ", " uStar ")" =>
  (⨆ u : U, ⟪u, uStar⟫ₚ + upperPerturbationFunction G u)

-- Proof sketch: expand the Fenchel conjugate of `- upperPerturbationFunction G` by
-- `convexConjugate_eq_iSup_pairing_sub`; then rewrite subtraction on `WithBotTop α` as addition
-- of the negation and simplify `-(- upperPerturbationFunction G u)`.
/-- The source shifted supremum from Definition 6.30.12 is exactly the Fenchel conjugate of the
negated upper perturbation function, evaluated at `u⋆`. -/
theorem shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction
    (G : U → X → WithBotTop α) (uStar : UStar) :
    shiftedSup(G, uStar) = (- upperPerturbationFunction G)⋆ uStar := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  refine iSup_congr ?_
  intro u
  rw [WithBotTop.sub_eq_add_neg]
  simp

namespace IsConcaveKuhnTuckerVector

variable [Zero U]
variable {G : U → X → WithBotTop α} {uStar : UStar}

-- Proof sketch: rewrite the source shifted supremum by
-- `shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction`, then use the defining equality
-- `supremum_eq_upperPerturbationFunction_zero`.
/-- Under the canonical additive structure on `WithBotTop α`, a concave Kuhn--Tucker vector
identifies the Fenchel conjugate of `- upperPerturbationFunction G` at `u⋆` with the unperturbed
upper perturbation value. -/
theorem convexConjugate_neg_upperPerturbationFunction_eq_upperPerturbationFunction_zero
    (h : IsConcaveKuhnTuckerVector G uStar) :
    (- upperPerturbationFunction G)⋆ uStar = upperPerturbationFunction G 0 := by
  rw [← shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction G uStar,
    h.supremum_eq_upperPerturbationFunction_zero]

end IsConcaveKuhnTuckerVector

end

end Bifunction

/-! ### Theorem_6_30_12 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.12 says that if `(P)` is the convex program attached to a closed
  proper convex bifunction `F`, then taking the dual program twice returns the original program.
  dual bifunction, the explicit iterated owner `adjoint U X (adjoint XStar UStar F)` for `F⋆⋆`,
  and `objective` for
  the zero-slice objective of the program attached to a bifunction, and
  `biadjointFunction_eq_closure` for double adjunction.
- `bridge/view`: the project does not package programs as separate structures; instead, the
  source program `(P)` is represented by `objective F`, and the dual of `(P*)` is represented by
  the zero-slice objective of the iterated adjoint bifunction
  `((adjoint U X (adjoint XStar UStar F))₀)`.

Domain-style sampling used here:
- `objective` from `Definition_6_29_12`;
- `adjoint` from `Definition_6_30_14`;
- `biadjointFunction_eq_closure` from `Theorem_6_30_11`.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner expressions already upstream: `(F)₀` and
  `adjoint U X (adjoint XStar UStar F)`;
- derived API added here: the source-facing identification of the dual of the dual program with
  the original program.

Redundant-source-assumption elimination:
- the source includes properness, but the program-level involutivity only uses the double-adjoint
  closure formula together with closedness of `Function.uncurry F`; properness does not change the
  mathematical content of this item's canonical owner statement.

Layer target: `bridge/view`, stated on the chapter's existing program owners rather than on a new
wrapper for convex or dual programs.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local instance : HasPairing XStar X 𝕜 :=
  HasPairing.swap (X := X) (Y := XStar) (L := 𝕜)

local instance : HasPairing UStar U 𝕜 :=
  HasPairing.swap (X := U) (Y := UStar) (L := 𝕜)

local notation "F⋆" => (adjoint XStar UStar F)
local notation "F⋆⋆" => (adjoint U X F⋆)

-- Proof sketch: the lower-semicontinuity hypothesis gives the canonical closure fixed-point
-- identity `cl F = F` on the graph function. Feed that into the existing Chapter 6 owner theorem
-- `biadjointFunction_eq_self_of_closure_eq_self`, then apply the zero-slice owner `objective`.
/-- Theorem 6.30.12: if `F` is a closed convex bifunction, then the dual of the dual program
attached to `F` is the original program, rendered canonically as equality between the zero-slice
objective of the iterated adjoint bifunction and the original zero-slice objective
`objective F`. -/
theorem objective_biadjointFunction_eq_objective
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F)) :
    (F⋆⋆)₀ = (F)₀ := by
  have hF_closure : cl F = F := by
    ext u x
    exact congrArg (fun g ↦ g (u, x)) (lowerSemicontinuousHull_eq_self hF_closed)
  simpa [objective] using congrArg objective
    (biadjointFunction_eq_self_of_closure_eq_self (F := F) hF_convex hF_closure)

end

end Bifunction

/-! ### Definition_6_30_13 (from Chap06) -/
noncomputable section

universe u v w z

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type w} {L : Type z}
variable [SupSet L] [Sub L] [Neg L] [HasPairing U UStar L]

open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.13 introduces the Lagrangian of the concave program attached
  to a bifunction `G`, with source formula `L(u⋆, x) = sup_u (⟪u, u⋆⟫ₚ + G u x)`.
- `core/canonical`: the owner abstraction for this supremum formula is the existing
  pairing-based Fenchel conjugate owner `convexConjugate`, applied to the negated `u`-slice
  `u ↦ -G u x`. This is the same mathematical object as the older product-kernel
  `partialSupremum` presentation, but it removes a duplicate local wheel and aligns the public
  API with the chapter's pairing/conjugation vocabulary.
- `bridge/view`: the source display formula is recovered by the immediate pointwise
  `iSup`-formula for `convexConjugate`.

Domain-style sampling used here:
- `HasPairing` and the notation `⟪·, ·⟫ₚ` from `Chap01.HasPairing` as the project owner for dual
  evaluation data;
- `convexConjugate` from `Chap03.Defn_12_2` as the canonical owner of
  `sup_u (⟪u, u⋆⟫ₚ - f u)`;
- `convexConjugate_eq_iSup_pairing_sub` from the same file as the canonical evaluation formula;
- `Function.partialSupremum` from `Chap01.Text_5_7_2` as the lower-level product-kernel owner
  that this file now avoids duplicating;
- `Bifunction.upperPerturbationFunction` from `Definition_6_30_11` as the neighboring
  slice-supremum owner pattern in Chapter 6.

Primitive data vs derived API:
- primitive ambient pairing data: `[HasPairing U UStar L]`;
- primitive bifunction data: `G : U → X → L`;
- source-facing owner introduced here: `Bifunction.lagrangian G`;
- core owner reused upstream: `convexConjugate (fun u ↦ -G u x)` on each `x`-slice;
- derived API: the source `iSup` formula `⨆ u, ⟪u, u⋆⟫ₚ + G u x` under additive
  assumptions, together with the weaker bridge formula `⨆ u, ⟪u, u⋆⟫ₚ - (-G u x)` used when
  only subtraction/negation is available.

Layer target: `source-facing`. The source genuinely names a Lagrangian attached to `G`, but the
definition is now expressed as a thin bridge to the canonical conjugate owner rather than as a
parallel local `partialSupremum` construction.
-/

/-- Definition 6.30.13: the Lagrangian of the concave program associated with a bifunction `G`,
implemented canonically as the Fenchel conjugate of the negated `u`-slice `u ↦ -G u x`. Its
source formula is `sup_u (⟪u, u⋆⟫ₚ + G u x)`. -/
abbrev lagrangian (G : U → X → L) : UStar → X → L :=
  fun uStar x ↦ (fun u ↦ -G u x)⋆ uStar

/-- Pointwise owner form of Definition 6.30.13: at each fixed `x`, `lagrangian G` is the Fenchel
conjugate of the negated slice `u ↦ -G u x`. -/
@[simp] theorem lagrangian_apply
    (G : U → X → L) (uStar : UStar) (x : X) :
    lagrangian G uStar x = (fun u ↦ -G u x)⋆ uStar :=
  rfl

end

section SourceFormula

variable {U : Type u} {X : Type v} {UStar : Type w} {L : Type z}
variable [SupSet L] [SubtractionMonoid L] [HasPairing U UStar L]

open scoped Rockafellar

/-- Evaluating `lagrangian G` at `(u⋆, x)` gives Rockafellar's source formula
`sup_u (⟪u, u⋆⟫ₚ + G u x)`. -/
theorem lagrangian_eq_iSup_pairing_add
    (G : U → X → L) (uStar : UStar) (x : X) :
    lagrangian G uStar x =
      ⨆ u : U, ⟪u, uStar⟫ₚ + G u x := by
  simpa [sub_neg_eq_add] using
    convexConjugate_eq_iSup_pairing_sub (fun u ↦ -G u x) uStar

end SourceFormula

section Bridge

variable {U : Type u} {X : Type v} {UStar : Type w} {L : Type z}
variable [SupSet L] [Sub L] [Neg L] [HasPairing U UStar L]

open scoped Rockafellar

/-- Bridge form of the Lagrangian evaluation formula, keeping only the primitive codomain
operations needed by the conjugate owner:
`sup_u (⟪u, u⋆⟫ₚ - (-G u x))`. This is the form used for order-dual downstream bridges such as
Chapter 7's infimum formulas. -/
theorem lagrangian_eq_iSup_pairing_sub
    (G : U → X → L) (uStar : UStar) (x : X) :
    lagrangian G uStar x =
      ⨆ u : U, ⟪u, uStar⟫ₚ - (-G u x) := by
  simpa using convexConjugate_eq_iSup_pairing_sub (fun u ↦ -G u x) uStar

end Bridge

end Bifunction

/-! ### Theorem_6_30_13 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable [AddCommGroup U] [Preorder U] [Module 𝕜 U]
variable [AddCommGroup X] [PartialOrder X] [IsOrderedAddMonoid X] [Module 𝕜 X]
variable [PosSMulMono 𝕜 X]
variable [AddCommGroup UStar] [PartialOrder UStar] [IsOrderedAddMonoid UStar] [Module 𝕜 UStar]
variable [PosSMulMono 𝕜 UStar]
variable [AddCommGroup XStar] [Preorder XStar] [Module 𝕜 XStar]
variable [HasPairing U UStar 𝕜]
variable [HasPairing XStar X 𝕜]

local instance : HasPairing X XStar 𝕜 :=
  HasPairing.swap (X := XStar) (Y := X) (L := 𝕜)

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 6.30.13 computes the adjoint of the polyhedral bifunction attached to
  the linear program data `(aStar, a, A)`, together with a dual-side linear map `AT`.
- `core/canonical`: Chapter 6 already owns the LP perturbation bifunction as
  `linearProgram`, the duality transform as `adjoint`, and the LP feasible-region owner as
  `linearProgramFeasibleSet`. The dual feasible region in the theorem is exactly the same owner,
  written intrinsically with `AT : UStar →ₗ[𝕜] XStar` as
  `linearProgramFeasibleSet xStar (-AT) aStar`, so the theorem surface should reuse that owner
  instead of a duplicate raw set comprehension.
- `bridge/view`: the source's displayed inequalities
  `0 ≤ uStar ∧ aStar - AT uStar ≥ xStar` are the explicit membership condition obtained by
  expanding that same owner, so they remain only in explanatory prose rather than as a second
  public set definition. The compatibility between `A` and `AT` is recorded explicitly by
  `hAT : ∀ x y, ⟪A x, y⟫ₚ = ⟪x, AT y⟫ₚ`.

Domain-style sampling used here:
- `linearProgram` and `linearProgram_apply` from `Definition_6_30_18`;
- `linearProgramFeasibleSet` and `mem_linearProgramFeasibleSet_iff` from `Definition_6_30_18`;
- `adjoint` from `Definition_6_30_14`;
- the indicator owner `δ[𝕜](· | C)` from `Defintion_4_8_1`;
- the canonical pairing owner `⟪·, ·⟫ₚ`;
- linear-map expressions `A x` and `AT uStar`.

Layer target: `source-facing`, keeping the source formula but reusing the canonical owners
`linearProgram aStar a A`, `adjoint`, and the dual feasible-set owner
`linearProgramFeasibleSet xStar (-AT) aStar` instead of preserving coordinate-level wrappers.
-/

-- Proof sketch: start from the defining formula
-- `adjoint F xStar uStar = -((Function.uncurry F)⋆ (-uStar, xStar))`, substitute
-- `F = linearProgram aStar a A`, and compute the conjugate by separating the
-- nonnegativity constraint on `x` from the slack-variable description of `a - A x ≤ u`. The
-- pairing-compatibility identity `hAT` converts `⟪A x, uStar⟫` into `⟪x, AT uStar⟫`.
/-- Theorem 6.30.13: the adjoint of the canonical LP owner
`linearProgram aStar a A`,
equivalently `(u, x) ↦ ⟪aStar, x⟫ + δ[𝕜](x | 0 ≤ x, a ≤ A x + u)`, is
`(xStar, uStar) ↦ ⟪a, uStar⟫ - δ[𝕜](uStar | linearProgramFeasibleSet xStar (-AT) aStar)`,
where membership in that owner is exactly the source condition
`0 ≤ uStar ∧ aStar - AT uStar ≥ xStar`, under the pairing compatibility
`∀ x y, ⟪A x, y⟫ₚ = ⟪x, AT y⟫ₚ`. -/
theorem adjointFunction_linearProgram_apply
    (aStar xStar : XStar) (a : U) (uStar : UStar)
    (A : X →ₗ[𝕜] U) (AT : UStar →ₗ[𝕜] XStar)
    (hAT : ∀ x : X, ∀ y : UStar, (⟪A x, y⟫ₚ : 𝕜) = ⟪x, AT y⟫ₚ) :
    (linearProgram aStar a A)⋆ xStar uStar =
      (⟪a, uStar⟫ₚ : WithBotTop 𝕜) -
        δ[𝕜](uStar | linearProgramFeasibleSet xStar (-AT) aStar) := by
  sorry

-- Proof sketch: rewrite the indicator form in
-- `adjointFunction_linearProgram_apply`. On the feasible set the indicator is `0`, so the value
-- is `⟪a, uStar⟫`; outside the feasible set the indicator is `⊤`, and subtracting `⊤` in
-- `WithBotTop 𝕜` yields `⊥`, i.e. `-∞`.
/-- Equivalent case-split form of the adjoint value for the canonical LP bifunction, phrased using
the reused dual feasible-set owner. This owner membership is equivalent to the source inequalities
`0 ≤ uStar ∧ aStar - AT uStar ≥ xStar`, under the pairing compatibility
`∀ x y, ⟪A x, y⟫ₚ = ⟪x, AT y⟫ₚ`. -/
theorem adjointFunction_linearProgram_apply_eq_ite
    (aStar xStar : XStar) (a : U) (uStar : UStar)
    (A : X →ₗ[𝕜] U) (AT : UStar →ₗ[𝕜] XStar)
    (hAT : ∀ x : X, ∀ y : UStar, (⟪A x, y⟫ₚ : 𝕜) = ⟪x, AT y⟫ₚ) :
    (linearProgram aStar a A)⋆ xStar uStar =
      if uStar ∈ linearProgramFeasibleSet xStar (-AT) aStar then
        (⟪a, uStar⟫ₚ : WithBotTop 𝕜)
      else
        ⊥ := by
  rw [adjointFunction_linearProgram_apply (aStar := aStar) (xStar := xStar) (a := a)
    (uStar := uStar) (A := A) (AT := AT) hAT]
  by_cases hmem : uStar ∈ linearProgramFeasibleSet xStar (-AT) aStar
  · have hnot : uStar ∉ (linearProgramFeasibleSet xStar (-AT) aStar)ᶜ := by
      simpa using hmem
    rw [if_pos hmem, Set.indicator_of_notMem hnot]
    calc
      (⟪a, uStar⟫ₚ : WithBotTop 𝕜) - 0
          = (⟪a, uStar⟫ₚ : WithBotTop 𝕜) + (-0) := by
            rw [WithBotTop.sub_eq_add_neg]
      _ = (⟪a, uStar⟫ₚ : WithBotTop 𝕜) + 0 := by
            rw [WithBotTop.neg_zero]
      _ = (⟪a, uStar⟫ₚ : WithBotTop 𝕜) := by
            rw [add_zero]
  · have hcompl : uStar ∈ (linearProgramFeasibleSet xStar (-AT) aStar)ᶜ := by
      simpa using hmem
    rw [if_neg hmem, Set.indicator_of_mem hcompl]
    exact (WithBotTop.sub_top (x := (⟪a, uStar⟫ₚ : WithBotTop 𝕜)))

end

end Bifunction

/-! ### Definition_6_30_14 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar]
variable [HasPairing (U × X) (UStar × XStar) L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.14 introduces the adjoint bifunction associated to a bifunction
  `F`, with sign convention `F⋆(x⋆, u⋆) = - (uncurry F)⋆(-u⋆, x⋆)`.
- `core/canonical`: conjugation is already owned by `convexConjugate` (`(·)⋆`) at the pairing
  layer, so the primitive owner here should be this thin sign/currying bridge on the same codomain
  layer rather than a separate `WithBotTop`-specific package.
- `bridge/view`: the source writes the adjoint itself as `F⋆` and its biadjoint as `F⋆⋆`, so the
  public surface here exposes those scoped postfix notations. The raw owner remains the explicit
  map `adjoint F` because the dual parameters are not recoverable from `F` alone. Any
  swapped operational view is the canonical `Function.swap (F⋆)`, not a second bifunction owner.

Domain-style sampling used here:
- `convexConjugate` / `(·)⋆` from `Chap03.Defn_12_2`;
- product pairing owner from `Chap01.HasPairing`;
- `(·)₀` from `Chap06.Definition_6_29_12`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `adjoint F : XStar → UStar → L`;
- derived API: the optional scoped source-facing notations `F⋆` and `F⋆⋆` when the ambient dual
  parameters are already determined, together with the immediate pointwise and zero-slice
  simplification theorems stated on the explicit owner `adjoint F`, since the
  dual parameters are not recoverable from `F` alone.

Layer target: `source-facing` on the pairing-based codomain owner layer, avoiding an unnecessary
specialization to `WithBotTop α`, `EReal`, or inner-product self-duality.
-/

/-- Definition 6.30.14: the adjoint bifunction attached to `F`, expressed canonically as a
sign/currying bridge from the conjugate of `Function.uncurry F`. -/
def adjoint (F : U → X → L) : XStar → UStar → L :=
  fun xStar uStar ↦ - (Function.uncurry F)⋆ (-uStar, xStar)

end

end Bifunction

namespace Rockafellar

/- Rockafellar's optional adjoint-bifunction notation. In `open scoped Rockafellar`, a bifunction
term `F` may be written as `F⋆`, and when both adjoint pairings are in scope its biadjoint may be
written as `F⋆⋆`, when local type information already determines the dual ambient types. The
explicit owner remains `Bifunction.adjoint F`, and the self-dual biconjugate surface
is `(F⋆⋆ : U → X → L)` when that type ascription is needed for disambiguation. -/
scoped[Rockafellar] postfix:max "⋆" => fun F ↦ Bifunction.adjoint F
scoped[Rockafellar] postfix:max "⋆⋆" =>
  fun F ↦ Bifunction.adjoint (Bifunction.adjoint F)
scoped[Rockafellar] notation:max "adjoint " XStar " " UStar " " F =>
  (Bifunction.adjoint (XStar := XStar) (UStar := UStar) F)

end Rockafellar

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar]
variable [HasPairing (U × X) (UStar × XStar) L]

/-- Evaluating the adjoint bifunction gives the defining conjugate formula. -/
@[simp] theorem adjoint_apply
    (F : U → X → L) (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar = - ((Function.uncurry F)⋆ (-uStar, xStar)) :=
  rfl

section

variable [Zero XStar]

-- Proof sketch: evaluate the zero slice of `F⋆` at `u⋆`, then unfold `adjoint`.
/-- Evaluating the dual zero-slice objective `(F⋆)₀` at `u⋆` gives the source formula
`- (uncurry F)⋆ (-u⋆, 0)`. -/
@[simp] theorem objective_adjoint_apply
    (F : U → X → L) (uStar : UStar) :
    ((adjoint XStar UStar F)₀ uStar) =
      - ((Function.uncurry F)⋆ (-uStar, (0 : XStar))) := by
  rfl

end

end

end Bifunction

/-! ### Theorem_6_30_14 (from Chap06) -/
/-!
Source/core/bridge triage:

- `source-facing`: Section 30, item 6.30.14 is the adjoint bifunction attached to a bifunction
  `F`, not a separate theorem-level identity.
- `core/canonical`: that owner already lives in
  `ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14` as
  `Bifunction.adjoint`.
- `bridge/view`: the pointwise and zero-slice formulas are already the companion API
  `Bifunction.adjoint_apply` and `Bifunction.objective_adjoint_apply` in the same owner file.

Domain-style sampling used here:
- `Bifunction.adjoint` from `Definition_6_30_14`;
- `Bifunction.adjoint_apply` from `Definition_6_30_14`;
- `Bifunction.objective_adjoint_apply` from `Definition_6_30_14`.

Primitive data vs derived API:
- primitive owner for item 6.30.14: `Bifunction.adjoint`;
- derived API already upstream: its pointwise and zero-slice evaluation lemmas;
- no additional theorem-level owner belongs in this file.

Layer target: `core/canonical recall/use`.
-/

/- Section 30, item 6.30.14 is already formalized by the canonical owner
`Bifunction.adjoint` in `Definition_6_30_14`. There is no separate theorem declaration here. -/
recall Bifunction.adjoint

/-! ### Definition_6_30_15 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [SupSet L] [InfSet L] [Sub L]
variable [HasPairing U UStar L] [HasPairing X XStar L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.15 introduces the adjoint of a concave bifunction on the dual
  variables `(x⋆, u⋆)`.
- `core/canonical`: for fixed `x⋆`, the project already owns this mathematics through the
  conjugacy layer `concaveConjugate` followed by `convexConjugate`: first conjugate the slice
  `G u` in `x`, then conjugate the resulting `u`-slice in `u`.
- `bridge/view`: the textbook double-`⨆` formula, plus under stronger right-negation
  compatibility on the `X`-pairing the graph-function bridge to
  `convexConjugate (- Function.uncurry G)`.

Domain-style sampling used here:
- the pairing owners `HasPairing U UStar L` and `HasPairing X XStar L`, with notation `⟪·, ·⟫ₚ`;
- `convexConjugate` from `Chap03.Defn_12_2`, which owns the outer `u`-supremum;
- `concaveConjugate` from `Definition_6_30_4`, which owns the inner `x`-slice conjugation;
- `Bifunction.adjoint` from `Definition_6_30_14`, whose sign-twisted convex owner is
  related but mathematically distinct.

Primitive data vs derived API:
- primitive data: a bifunction `G : U → X → L`;
- primitive ambient data: canonical pairings from `HasPairing`;
- source-facing owner: `concaveAdjoint XStar UStar G : XStar → UStar → L`;
- core owner reused upstream:
  `fun xStar ↦ convexConjugate (fun u ↦ (G u)∗ xStar)`;
- derived API: the outer-conjugate evaluation formula on the generic pairing-codomain layer, then
  in the stronger `WithBotTop` specialization below the textbook double-`⨆` formula and the
  graph-function bridge theorem.

Layer target: `source-facing`, but as a thin bridge to the existing conjugacy layer rather than a
new primitive wheel.
-/

/-- Definition 6.30.15: the adjoint of a concave bifunction `G`, written in the source order
`x⋆ ↦ G*_{x⋆}` on the dual variables. Canonically, for each fixed `x⋆`, this is the Fenchel
conjugate in `u` of the slice `u ↦ (G u)∗ x⋆`. -/
abbrev concaveAdjoint
    (XStar : Type v') (UStar : Type u')
    [HasPairing U UStar L] [HasPairing X XStar L]
    (G : U → X → L) : XStar → UStar → L :=
  fun xStar ↦ (fun u ↦ (G u)∗ xStar)⋆

/- Evaluating `concaveAdjoint G` recalls the canonical outer-conjugate owner. -/
@[simp] theorem concaveAdjoint_apply
    (G : U → X → L)
    (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      (fun u ↦ (G u)∗ xStar)⋆ uStar :=
  rfl

/- Evaluating the outer conjugate gives the canonical one-variable supremum formula. -/
theorem concaveAdjoint_eq_iSup_pairing_sub_concaveConjugate
    (G : U → X → L)
    (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      ⨆ u : U, ⟪u, uStar⟫ₚ - (G u)∗ xStar := by
  simpa [concaveAdjoint] using
    convexConjugate_eq_iSup_pairing_sub (fun u ↦ (G u)∗ xStar) uStar

section ConvexConjugateBridge

variable [Add L] [Neg L] [Neg XStar] [HasPairingNegRight X XStar L]

-- Proof sketch: rewrite `concaveAdjoint` by the derived double-`⨆` source formula, then
-- expand `convexConjugate (- Function.uncurry G)` at `(u⋆, -x⋆)` and use `pairing_neg_right` on
-- the `X`-pairing inside the canonical product pairing.
/-- Under the canonical right-negation compatibility on the `X`-pairing, and with the canonical
product pairing between `(U × X)` and `(UStar × XStar)`, the source concave adjoint is exactly
the Fenchel conjugate of the negated graph function `- Function.uncurry G` evaluated at
`(u⋆, -x⋆)`. This
keeps the source-facing owner while exposing the stronger Chapter 12 bridge when the extra sign
structure is available. -/
theorem concaveAdjoint_eq_convexConjugate_neg_uncurry
    (G : U → X → L) :
    concaveAdjoint XStar UStar G =
      fun (xStar : XStar) (uStar : UStar) ↦
        convexConjugate (- Function.uncurry G) (uStar, -xStar) := sorry

@[simp] theorem concaveAdjoint_eq_convexConjugate_neg_uncurry_apply
    (G : U → X → L) (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      convexConjugate (- Function.uncurry G) (uStar, -xStar) := by
  simpa using
    congrFun
      (congrFun
        (concaveAdjoint_eq_convexConjugate_neg_uncurry (G := G)) xStar)
      uStar

end ConvexConjugateBridge

end

section WithBotTop

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {α : Type w}
variable [ConditionallyCompleteLinearOrder α]
variable [HasPairing U UStar α] [HasPairing X XStar α]

section TextbookFormula

variable [AddCommGroup α]

/-- Evaluating `concaveAdjoint G` gives the textbook formula
`sup_u sup_x (G(u, x) - pairing x x⋆ + pairing u u⋆)`. -/
theorem concaveAdjoint_eq_iSup_iSup
    (G : U → X → WithBotTop α)
    (xStar : XStar) (uStar : UStar) :
    concaveAdjoint XStar UStar G xStar uStar =
      ⨆ u : U, ⨆ x : X,
        G u x - ⟪x, xStar⟫ₚ + ⟪u, uStar⟫ₚ := sorry
end TextbookFormula

end WithBotTop

end Bifunction

/-! ### Theorem_6_30_15 (from Chap06) -/
noncomputable section

open Function
open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.15 identifies the primal perturbation function `inf F`, the dual
  upper perturbation function `sup F*`, the zero-slice objectives `F₀` and `F*₀`, and the two
  conjugacy correspondences between them.
  `perturbationFunction`, `upperPerturbationFunction`, `(·)₀`, `adjoint`,
  `concaveConjugate`, the Fenchel conjugate `(·)⋆`, the convex closure `cl(·)`, and the concave
  closure `concaveClosure`.
- `bridge/view`: this file contributes only theorem-level identities between those existing
  owners; it introduces no new wrapper around primal or dual programs.

Primary mathematical domain:
- convex/concave duality for bifunctions. The first conjugacy identity is a
  formal owner bridge on a generic pairing codomain layer `L`; the remaining biconjugacy and
  closure identities use the chapter `WithBotTop 𝕜` closure owners. The second identity uses the
  finite-dimensional scalar-parametric biconjugacy layer on `U`, while the final objective-side
  identities stay on the intrinsic scalar-parametric paired `X`/`XStar` owner layer provided by
  `adjoint` and `f⋆` under `HasPairing.swap`.

Domain-style sampling used here:
- `perturbationFunction` and `(·)₀` from Definitions 6.29.1 and 6.29.12;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` and `objective_adjoint_apply` from Definition 6.30.14;
- `concaveConjugate`, `(·)⋆`, `cl(·)`, and `concaveClosure`;
- `Function.IsConcave.biconjugate_eq_concaveClosure` from Theorem 6.30.3.

Primitive data vs derived API:
- primitive input: a bifunction `F`, at the generic codomain layer for the first identity and at
  the `WithBotTop 𝕜` layer for the closure identities (specializing to `EReal` at `𝕜 = ℝ`);
- primitive owners already upstream: `perturbationFunction F`, `(F)₀`,
  `upperPerturbationFunction (F⋆)`, and the dual zero-slice objective `(F⋆)₀`;
- derived API added here: the four source conjugacy identities relating those owners.

Layer target: `bridge/view`. The public statements stay on the chapter's canonical owner
declarations and use the Chapter 6 source notation `(·)₀` and `⋆` on the theorem surface,
avoiding any auxiliary package for the primal or dual programs.
-/

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Add L] [Sub L] [Neg L] [InfSet L] [SupSet L]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable (F : U → X → L)

local notation "F⋆" => adjoint XStar UStar F

-- Proof sketch: evaluate `(F⋆)₀` using `objective_adjoint_apply`, then rewrite the
-- right-hand side as the defining `iInf` formula for the concave conjugate of
-- `- perturbationFunction F`. The slice infimum in the perturbation variable is exactly
-- `perturbationFunction F`.
/-- Theorem 6.30.15, first conjugacy identity: on the canonical pairing-based codomain layer,
the dual zero-slice objective `(F⋆)₀` is the concave conjugate `(- perturbationFunction F)∗`
of the primal perturbation function. -/
theorem concaveConjugate_neg_perturbationFunction_eq_objective_adjointFunction
    :
    (- perturbationFunction F)∗ = (F⋆)₀ := sorry

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U] [FiniteDimensional 𝕜 U]
variable [Zero XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

-- Proof sketch: combine the previous conjugacy identity with the Chapter 6 concave biconjugacy
-- theorem applied to `- perturbationFunction F`. The only owner-level input is concavity of
-- `- perturbationFunction F`, equivalently convexity of `perturbationFunction F` on `U`.
-- Unfolding `concaveClosure` gives the displayed right-hand side `- cl(perturbationFunction F)`.
/-- The concave conjugate of the dual zero-slice objective is the negative closure of the primal
perturbation function. This is stated on the finite-dimensional scalar-parametric pairing layer on
`U` together with convexity of the primal perturbation function on `U`; the `X`-side assumptions
are only the primitive paired owner data needed to form `adjoint XStar U F`. -/
theorem concaveConjugate_objective_adjointFunction_eq_neg_cl_perturbationFunction
    (hp_convex : (perturbationFunction F).IsConvex 𝕜) :
    ((F⋆)₀)∗ = - cl(perturbationFunction F) := sorry

end

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {XStar : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace XStar]
variable [HasLinearPairing U U 𝕜] [HasContinuousPairing U U 𝕜]
variable [HasPairing X XStar 𝕜]
variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar U F

local notation "IsClosedProperConvex[" 𝕜 "]" =>
  Function.IsClosedProperConvex (𝕜 := 𝕜)

local instance : HasPairing XStar X (WithBotTop 𝕜) :=
  HasPairing.swap (X := X) (Y := XStar) (L := WithBotTop 𝕜)

/- Theorem 6.30.15 is recorded above as the generic owner-bridge identity, then the
`U`-side closed-value identity on the scalar-parametric `WithBotTop 𝕜` layer, and finally the two
closed-proper companion identities for the reverse direction. -/

-- Proof sketch: use the closed-proper-convex fixed-point theorem for the double adjoint
-- bifunction to identify `F` with the convex conjugate picture coming from the dual upper
-- perturbation function. The resulting equality is exactly the source formula
-- `(- sup F*)* = F₀`.
/-- For a closed proper convex bifunction, the primal zero-slice objective is the swapped-pairing
Fenchel conjugate of the convex function `- sup F*`, written directly as
`((- supᵇ(F⋆))⋆ : X → WithBotTop 𝕜)`. -/
theorem convexConjugateSwap_neg_upperPerturbationFunction_adjoint_eq_objective
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    ((- supᵇ(F⋆))⋆ : X → WithBotTop 𝕜) = (F)₀ := sorry

-- Proof sketch: apply convex biconjugacy to the closed proper convex function
-- `- upperPerturbationFunction (F⋆)` and combine it with the previous equality.
-- Rewriting the closure of a negated concave function through `concaveClosure` yields the
-- displayed right-hand side.
/-- For a closed proper convex bifunction, the Fenchel conjugate of the primal zero-slice
objective is the negative concave closure of the dual upper perturbation function. -/
theorem convexConjugate_objective_eq_neg_concaveClosure_upperPerturbationFunction_adjoint
    (hF : IsClosedProperConvex[𝕜] (uncurry F)) :
    (((F)₀)⋆ : XStar → WithBotTop 𝕜) =
      - concaveClosure (supᵇ(F⋆)) := sorry

end

end Bifunction

/-! ### Definition_6_30_16 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar] [Zero XStar]
variable [HasPairing (U × X) (UStar × XStar) L]
variable (F : U → X → L)

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.16 says that the dual program attached to a bifunction `F`
  uses as objective the zero slice of the adjoint bifunction `F⋆`.
- `core/canonical`: the owner abstractions are already `adjoint XStar UStar F` for `F⋆` and
  `(·)₀` / `objective` for the zero-slice objective.
- `bridge/view`: there is no second owner here. The source dual objective is exactly the existing
  composite owner `((adjoint XStar UStar F)₀)`, equivalently `(F⋆)₀` on the theorem
  surface when the ambient dual types are already determined.

Primary mathematical domain:
- convex duality for bifunctions, specifically the adjoint-dual objective in Chapter 6.

Domain-style sampling used here:
- `Bifunction.objective` and `(·)₀` from `Definition_6_29_12`;
- `Bifunction.objective_apply` from `Definition_6_29_12`;
- `Bifunction.adjoint` and `(·)⋆` from `Definition_6_30_14`;
- `Bifunction.objective_adjoint_apply` from `Definition_6_30_14`.

Best owner abstraction:
- the canonical owner expression `((adjoint XStar UStar F)₀) :
    UStar → L`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → L`;
- primitive owner reused directly: `adjoint XStar UStar F`;
- derived/source-facing view: its zero slice `((adjoint XStar UStar F)₀)`, written
  suggestively as `(F⋆)₀` when the dual ambient parameters are inferable.

Layer target: `core/canonical recall/use`.
-/

/- Definition 6.30.16 is the existing Chapter 6 owner expression for the zero-slice objective of
the adjoint bifunction. No separate `dualObjective` declaration is introduced here. -/
#check (((F⋆ : XStar → UStar → L)₀) : UStar → L)

end

end Bifunction

/-! ### Theorem_6_30_16 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.16 states that for a closed convex bifunction program `(P)` and
  its adjoint dual `(P*)`, primal normality, dual normality, and equality of the primal and dual
  values are equivalent.
- `core/canonical`: the relevant Chapter 6 owners already present are
  `perturbationFunction`, `upperPerturbationFunction`, `adjoint`, and the Chapter 2
  closure owners `cl(·)` and `- cl(- ·)`.
- `bridge/view`: the shortest faithful theorem surface keeps the source point-value equation
  directly as `perturbationFunction F 0 = q 0`.

Primary mathematical domain:
- convex duality for closed convex bifunctions on scalar-parametric paired spaces.

Domain-style sampling used here:
- `perturbationFunction` from Definition 6.29.1;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` from Definition 6.30.14;
- the closure owners `cl(·)` and `- cl(- ·)` at the primal/dual base points.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner expressions already upstream: `perturbationFunction F`,
  `upperPerturbationFunction F⋆`, and their closure formulas at `0`;
- derived API added here: the TFAE equivalence between primal normality, dual normality, and
  zero duality gap.

Layer target: `bridge/view`, stated directly on the canonical owner expressions rather than
introducing a new wrapper for primal or dual programs.

Ambient-vs-intrinsic topology choice:
- this theorem is intentionally phrased with the ambient closure owners `cl(·)` and `- cl(- ·)`
  because those are the Chapter 6 normality owners used by the surrounding closure/conjugacy
  bridge files; no project-level intrinsic/relative replacement owner is established nearby.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup UStar] [Module 𝕜 UStar]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local notation "F⋆" => adjoint XStar UStar F
local notation "p" => perturbationFunction F
local notation "q" => upperPerturbationFunction F⋆

-- Proof sketch: once the closed-convex bridge identities
-- `cl(p) 0 = q 0` and `(- cl(-q)) 0 = p 0` are available, each normality clause is equivalent
-- to the shared middle equality `p 0 = q 0`, so the three source conditions lie in one
-- `List.TFAE` class. The adjoint owner is parameterized by the explicit dual-side space `UStar`
-- rather than a self-dual `U`.
/-- Theorem 6.30.16: for a closed convex bifunction `F`, the following are equivalent:
(a) the convex program `(P)` associated with `F` is normal, rendered canonically as
`p 0 = cl(p) 0`;
(b) the dual concave program `(P*)` is normal, rendered canonically as
`q 0 = (- cl(-q)) 0`;
(c) `inf F 0 = sup F* 0`, rendered canonically as `p 0 = q 0`, equivalently equality of the
primal and dual optimal values. -/
theorem primalNormal_dualNormal_zeroDualityGap_tfae
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F)) :
    List.TFAE
      [p 0 = cl(p) 0,
        q 0 = (- cl(-q)) 0,
        p 0 = q 0] := sorry

end

end Bifunction

/-! ### Definition_6_30_17 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable (UStar : Type u') (XStar : Type v')
variable [AddGroup α] [ConditionallyCompleteLattice α]
variable [Neg UStar] [Zero XStar]
variable [HasPairing U UStar α] [HasPairing X XStar α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.17 introduces the notion of a Kuhn--Tucker vector for the dual
  program `(P*)` associated with a bifunction `F`.
- `core/canonical`: the Chapter 6 owner layer already present is the adjoint notation `F⋆`
  together with `upperPerturbationFunction` for the dual value function
  `x⋆ ↦ sup_u F⋆(x⋆, u⋆)`, and the Chapter 12 Fenchel owner `convexConjugate` applied to
  `- upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α)` once the pairing is read in
  the reversed orientation `HasPairing XStar X α`.
- `bridge/view`: the source's displayed two-variable supremum is kept as the source-facing slice
  expansion of that canonical conjugate owner; there is no separate public `dualUpper`,
  `dualOptimalValue`, or finiteness wrapper.

Domain-style sampling used here:
- `Bifunction.IsKuhnTuckerVector` from Definition 6.29.19 as the primal-side owner pattern;
- `Bifunction.upperPerturbationFunction` from Definition 6.30.11;
- `Bifunction.adjoint` and the notation `F⋆` from Definition 6.30.14;
- `convexConjugate` and `convexConjugate_eq_iSup_pairing_sub` from `Chap03.Defn_12_2`;
- the zero-slice owner recall from Definition 6.30.16.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → WithBotTop α` and a primal vector `x : X`;
- primitive owner introduced here: `IsDualKuhnTuckerVector UStar XStar F x`;
- primitive fields: interval-membership finiteness of the defining supremum and its equality
  with the dual value `upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0`;
- derived API: bundled finiteness, finiteness of that dual value, and the bridge from the source
  supremum to the canonical Fenchel conjugate owner.

Layer target: `source-facing`. The source genuinely defines a Kuhn--Tucker property of primal
vectors, so the class remains primitive on the source formula, while the companion conjugate layer
is read directly through `f⋆` under the swapped pairing `HasPairing.swap`.
-/

local notation "dualUpper(" F ")" =>
  (supᵇ((adjoint XStar UStar F : XStar → UStar → WithBotTop α)))

local notation "shiftedSup(" F ", " x ")" =>
  (⨆ xStar : XStar,
    ⟪x, xStar⟫ₚ + dualUpper(F) xStar)

local instance : HasPairing XStar X (WithBotTop α) :=
  HasPairing.swap (X := X) (Y := XStar) (L := WithBotTop α)

/-- Definition 6.30.17: a vector `x` is a Kuhn--Tucker vector for the dual program associated
with `F` when the supremum of the source dual expression
`x⋆ ↦ ⟪x, x⋆⟫ₚ + upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) x⋆` is finite and
equals the dual value `upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0`. -/
class IsDualKuhnTuckerVector (F : U → X → WithBotTop α) (x : X) : Prop where
  supremum_mem_Ioo : shiftedSup(F, x) ∈ Set.Ioo (⊥ : WithBotTop α) ⊤
  supremum_eq_upperPerturbationFunction_adjoint_zero :
    shiftedSup(F, x) = dualUpper(F) 0

omit [Zero XStar] in
/-- The source supremum from Definition 6.30.17 is exactly the Fenchel conjugate of the negated
dual upper-perturbation function, read directly through `f⋆` with the swapped pairing
`HasPairing.swap`. -/
theorem shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction_adjoint
    (F : U → X → WithBotTop α) (x : X) :
    shiftedSup(F, x) = ((- dualUpper(F))⋆ : X → WithBotTop α) x := by
  rw [convexConjugate_eq_iSup_pairing_sub
      (X := XStar) (Y := X) (L := WithBotTop α) (f := - dualUpper(F)) (y := x)]
  refine iSup_congr ?_
  intro xStar
  change ⟪x, xStar⟫ₚ + dualUpper(F) xStar =
      ((⟪xStar, x⟫ₚ : WithBotTop α) - (-dualUpper(F) xStar))
  change ⟪x, xStar⟫ₚ + dualUpper(F) xStar =
      (⟪x, xStar⟫ₚ - (-dualUpper(F) xStar))
  rw [WithBotTop.sub_eq_add_neg, neg_neg]

namespace IsDualKuhnTuckerVector

variable {F : U → X → WithBotTop α} {x : X}

/-- Lower finiteness bound from the defining interval-membership field. -/
theorem supremum_bot_lt (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ⊥ < shiftedSup(F, x) :=
  h.supremum_mem_Ioo.1

/-- Upper finiteness bound from the defining interval-membership field. -/
theorem supremum_lt_top (h : IsDualKuhnTuckerVector UStar XStar F x) :
    shiftedSup(F, x) < ⊤ :=
  h.supremum_mem_Ioo.2

/-- A dual Kuhn--Tucker vector makes the defining dual supremum finite. -/
theorem supremum_finite (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ⊥ < shiftedSup(F, x) ∧ shiftedSup(F, x) < ⊤ :=
  ⟨h.supremum_bot_lt, h.supremum_lt_top⟩

/-- A dual Kuhn--Tucker vector identifies the dual value
`upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0` with the defining supremum. -/
theorem upperPerturbationFunction_adjoint_zero_eq_supremum
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    dualUpper(F) 0 = shiftedSup(F, x) :=
  h.supremum_eq_upperPerturbationFunction_adjoint_zero.symm

/-- A dual Kuhn--Tucker vector identifies the swapped-pairing Fenchel conjugate
`((- upperPerturbationFunction (adjoint XStar UStar F))⋆ : X → WithBotTop α)` at `x`
with the dual value `upperPerturbationFunction (adjoint XStar UStar F) 0`. -/
theorem
    convexConjugate_neg_upperPerturbationFunction_adjoint_eq_upperPerturbationFunction_adjoint_zero
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ((- dualUpper(F))⋆ : X → WithBotTop α) x = dualUpper(F) 0 := by
  rw [← shiftedSup_eq_convexConjugate_neg_upperPerturbationFunction_adjoint UStar XStar F x,
    h.supremum_eq_upperPerturbationFunction_adjoint_zero]

/-- A dual Kuhn--Tucker vector forces the dual value
`upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0` to lie in the finite interval
`Set.Ioo (⊥ : WithBotTop α) ⊤`. -/
theorem upperPerturbationFunction_adjoint_zero_mem_Ioo
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    dualUpper(F) 0 ∈ Set.Ioo (⊥ : WithBotTop α) ⊤ := by
  rw [h.upperPerturbationFunction_adjoint_zero_eq_supremum]
  exact h.supremum_mem_Ioo

/-- A dual Kuhn--Tucker vector forces the dual value
`upperPerturbationFunction (F⋆ : XStar → UStar → WithBotTop α) 0` to be finite. -/
theorem upperPerturbationFunction_adjoint_zero_finite
    (h : IsDualKuhnTuckerVector UStar XStar F x) :
    ⊥ < dualUpper(F) 0 ∧ dualUpper(F) 0 < ⊤ := by
  exact h.upperPerturbationFunction_adjoint_zero_mem_Ioo

end IsDualKuhnTuckerVector

end

end Bifunction

/-! ### Theorem_6_30_17 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v w

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.17 lists ten sufficient conditions guaranteeing normality of both
  the primal convex program `(P)` attached to a closed convex bifunction `F` and its adjoint dual
  program `(P*)`.
- `core/canonical`: the Chapter 6 owner layer is already
  `perturbationFunction`, `upperPerturbationFunction`, `(·)⋆`, `(·)₀`,
  `IsStronglyConsistent`, `IsConsistent`, `IsKuhnTuckerVector`,
  `IsDualKuhnTuckerVector`, `minimumSet`, `Function.HasPolyhedralEpigraph`, and
  `IsClosedConvex`.
- `bridge/view`: the source normality statements are kept directly as the two closure identities
  `p 0 = cl(p) 0` and `q 0 = (-cl(-q)) 0`, rather than via a larger wrapper around the ten source
  hypotheses. The dual objective surface is expressed canonically by the Chapter 6 owner
  `((adjoint XStar UStar F)₀)`.

Primary mathematical domain:
- convex duality for closed convex bifunctions on paired scalar-parametric spaces.

Domain-style sampling used here:
- `IsStronglyConsistent` from Definition 6.29.10;
- `IsKuhnTuckerVector` from Definition 6.29.19;
- `upperPerturbationFunction` from Definition 6.30.11;
- `adjoint` / notation `(·)⋆` from Definition 6.30.14;
- `((adjoint XStar UStar F)₀)` from Definition 6.30.16;

Best owner abstraction:
- theorem-level sufficient conditions stated directly on those Chapter 6 owners, not a separate
  public predicate packaging the ten alternatives, and with closed-convexity stated on the
  canonical owner `IsClosedConvex`.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜` together with the
  closed-convex owner `IsClosedConvex F` when the clause hypothesis itself does not already force
  it;
- primitive/source-side sufficient conditions: the ten textbook clauses, each stated directly on
  the canonical owners above;
- derived conclusion: primal and dual normality, expressed by the two closure equalities at `0`.

Layer target: `source-facing`, split into atomic theorem surfaces for the ten source clauses.
-/

section

variable {𝕜 : Type w} {U : Type u} {X : Type v} {UStar : Type u} {XStar : Type v}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [Neg UStar]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

variable {F : U → X → WithBotTop 𝕜}

local notation "F⋆" => ((adjoint XStar UStar F) : XStar → UStar → WithBotTop 𝕜)
local notation "f₀" => (F)₀
local notation "d₀" => (((F⋆)₀) : UStar → WithBotTop 𝕜)
local notation "p" => perturbationFunction F
local notation "q" => upperPerturbationFunction (F⋆)
local notation "primalSublevel(" ξ ")" => (f₀ ⁻¹' Set.Iic ξ)
local notation "dualSuperlevel(" ξ ")" => (d₀ ⁻¹' Set.Ici ξ)
local notation "dualMaximizerSet" =>
  ({uStar : UStar | IsMaxOn d₀ Set.univ uStar} : Set UStar)

/-- Theorem 6.30.17 (1): under source clause `(a)`, strong consistency of the primal program
forces normality of both the primal perturbation function and the dual upper perturbation
function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_isStronglyConsistent
    (hF_closedConvex : IsClosedConvex F)
    (hstrong : IsStronglyConsistent 𝕜 F) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (2): under source clause `(b)`, strong consistency of the adjoint dual
program forces normality of both the primal perturbation function and the dual upper perturbation
function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_isStronglyConsistent_adjointFunction
    (hF_closedConvex : IsClosedConvex F)
    (hstrong : IsStronglyConsistent 𝕜 (F⋆)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (3): under source clause `(c)`, existence of a primal Kuhn--Tucker vector
forces normality of both the primal perturbation function and the dual upper perturbation
function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_exists_isKuhnTuckerVector
    (hF_closedConvex : IsClosedConvex F)
    (hKT : ∃ uStar : UStar, IsKuhnTuckerVector F uStar) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (4): under source clause `(d)`, existence of a dual Kuhn--Tucker vector
forces normality of both the primal perturbation function and the dual upper perturbation
function at `0`, rendered on the canonical Chapter 6 source-facing dual owner
`IsDualKuhnTuckerVector`. The ambient closed-convex hypothesis is stated on the canonical owner
`IsClosedConvex F`. -/
theorem primalNormal_and_dualNormal_of_exists_isDualKuhnTuckerVector
    (hF_closedConvex : IsClosedConvex F)
    (hdualKT : ∃ x : X, IsDualKuhnTuckerVector UStar XStar F x) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (5): under source clause `(e)`, a polyhedral epigraph for `uncurry F`
together with primal consistency forces normality of both the primal perturbation function and the
dual upper perturbation function at `0`. -/
theorem primalNormal_and_dualNormal_of_uncurry_hasPolyhedralEpigraph_and_isConsistent
    (hpoly : (Function.uncurry F).HasPolyhedralEpigraph)
    (hconsistent : IsConsistent F) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (6): under source clause `(f)`, a polyhedral epigraph for the
negative adjoint graph function together with dual consistency forces normality of both the
primal perturbation function and the dual upper perturbation function at `0`. -/
theorem
    primalNormal_and_dualNormal_of_adjoint_hasPolyhedralEpigraph_and_isConsistent
    [AddCommGroup UStar] [Module 𝕜 UStar]
    (hpoly : (-Function.uncurry (F⋆)).HasPolyhedralEpigraph)
    (hconsistent : IsConsistent (F⋆)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

variable [Bornology X] [Bornology UStar]

/-- Theorem 6.30.17 (7): under source clause `(g)`, a nonempty bounded primal sublevel set of the
zero-slice objective forces normality of both the primal perturbation function and the dual upper
perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_primalSublevel
    (hF_closedConvex : IsClosedConvex F)
    (ξ : WithBotTop 𝕜)
    (hsublevel_nonempty : (primalSublevel(ξ)).Nonempty)
    (hsublevel_bounded : Bornology.IsBounded (primalSublevel(ξ))) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (8): under source clause `(h)`, a nonempty bounded dual superlevel set of
the dual zero-slice objective forces normality of both the primal perturbation function and the
dual upper perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_dualSuperlevel
    (hF_closedConvex : IsClosedConvex F)
    (ξ : WithBotTop 𝕜)
    (hsuperlevel_nonempty : (dualSuperlevel(ξ)).Nonempty)
    (hsuperlevel_bounded : Bornology.IsBounded (dualSuperlevel(ξ))) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (9): under source clause `(i)`, a nonempty bounded minimum set of the primal
zero-slice objective forces normality of both the primal perturbation function and the dual upper
perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_minimumSet_objective
    (hF_closedConvex : IsClosedConvex F)
    (hminimum_nonempty : Set.Nonempty (minimumSet f₀))
    (hminimum_bounded : Bornology.IsBounded (minimumSet f₀)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Theorem 6.30.17 (10): under source clause `(j)`, a nonempty bounded maximizer set of the
dual zero-slice objective forces normality of both the primal perturbation function and the dual
upper perturbation function at `0` for a closed convex bifunction `F`. -/
theorem primalNormal_and_dualNormal_of_nonempty_bounded_dualMaximizerSet
    (hF_closedConvex : IsClosedConvex F)
    (hmaximum_nonempty : Set.Nonempty dualMaximizerSet)
    (hmaximum_bounded : Bornology.IsBounded dualMaximizerSet) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

/-- Any one of the ten sufficient clauses from Theorem 6.30.17 yields both primal and dual
normality at `0`. This aggregated bridge keeps the reusable disjunctive interface expected by
later Chapter 6 and Chapter 7 statements while the source-facing clauses remain split atomically
above. -/
theorem primalNormal_and_dualNormal_of_sufficientNormalityHypothesis
    [AddCommGroup UStar] [Module 𝕜 UStar]
    (hqual :
      (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 F) ∨
        (IsClosedConvex F ∧ IsStronglyConsistent 𝕜 (F⋆)) ∨
        (IsClosedConvex F ∧ ∃ uStar : UStar, IsKuhnTuckerVector F uStar) ∨
        (IsClosedConvex F ∧ ∃ x : X, IsDualKuhnTuckerVector UStar XStar F x) ∨
        ((Function.uncurry F).HasPolyhedralEpigraph ∧ IsConsistent F) ∨
        ((-Function.uncurry (F⋆)).HasPolyhedralEpigraph ∧ IsConsistent (F⋆)) ∨
        (IsClosedConvex F ∧
          ∃ ξ : WithBotTop 𝕜,
            (primalSublevel(ξ)).Nonempty ∧
              Bornology.IsBounded (primalSublevel(ξ))) ∨
        (IsClosedConvex F ∧
          ∃ ξ : WithBotTop 𝕜,
            (dualSuperlevel(ξ)).Nonempty ∧
              Bornology.IsBounded (dualSuperlevel(ξ))) ∨
        (IsClosedConvex F ∧
          Set.Nonempty (minimumSet f₀) ∧
            Bornology.IsBounded (minimumSet f₀)) ∨
        (IsClosedConvex F ∧
          Set.Nonempty dualMaximizerSet ∧
            Bornology.IsBounded dualMaximizerSet)) :
    p 0 = cl(p) 0 ∧ q 0 = (-cl(-q)) 0 :=
  sorry

end

end Bifunction
