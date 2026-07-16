import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

universe u v w

section

/-!
Source/core/bridge triage:

- `source-facing`: Text 21.0.1 introduces a system of convex inequalities by splitting the index
  set into weak constraints `I₁` and strict constraints `I₂`, with `WithTopBot` bounds `αᵢ` and
  convex left-hand sides `fᵢ`. Specializing the ambient module recovers the textbook
  finite-dimensional coordinate presentation.
- `core/canonical`: the underlying feasible-set owner is the Chapter 1 indexed owner
  `LinearConstraintRelation.feasibleSet`, together with `LinearConstraintRelation` and its single-
  constraint owner `LinearConstraintRelation.solutionSet`.
- `bridge/view`: the source-facing relation type `ConvexInequalityRelation` is the canonical
  two-relation slice of `LinearConstraintRelation`, and the bridge to the Chapter 1 owner is the
  evaluation pairing between a point `x : E` and a scalar-valued function `f : E → WithTopBot α`.

Domain-style sampling used here:
- `LinearConstraintRelation` and `LinearConstraintRelation.feasibleSet` from `Corollary_2_1_2`;
- `LinearConstraintRelation.solutionSet` from `Corollary_2_1_2`;
- `Function.IsConvex.convex_le` and `Function.IsConvex.convex_lt` from `Theorem_4_6`.

Primitive data vs derived API:
- primitive source data: the relation kind (`≤` or `<`), the convex family `fᵢ`, and the bounds
  `αᵢ`;
- canonical owner data: the Chapter 1 mixed-relation feasible-set owner fed by the evaluation
  pairing;
- derived API: the source-facing two-relation view, the single-constraint convexity theorem for
  convex functions, and the feasible-set convexity theorem.

Layer target: `bridge/view` for the relation/solution-set owners, with the convexity statements
kept as the genuinely new source-facing content.
-/

variable {E : Type u} {α : Type w}

/-- The two comparison relations appearing in a system of convex inequalities. -/
inductive ConvexInequalityRelation where
  /-- Weak convex inequality relation. -/
  | le
  /-- Strict convex inequality relation. -/
  | lt

namespace ConvexInequalityRelation

instance : Coe ConvexInequalityRelation LinearConstraintRelation :=
  ⟨fun relation ↦
    match relation with
    | .le => .le
    | .lt => .lt⟩

@[simp] theorem coe_le :
    ((.le : ConvexInequalityRelation) : LinearConstraintRelation) = .le :=
  rfl

@[simp] theorem coe_lt :
    ((.lt : ConvexInequalityRelation) : LinearConstraintRelation) = .lt :=
  rfl

/-- Constant all-weak relation family on an index type. -/
abbrev allLe {I : Sort v} : I → ConvexInequalityRelation :=
  fun _ ↦ .le

/-- Constant all-strict relation family on an index type. -/
abbrev allLt {I : Sort v} : I → ConvexInequalityRelation :=
  fun _ ↦ .lt

@[simp] theorem allLe_apply {I : Sort v} (i : I) :
    allLe i = ConvexInequalityRelation.le :=
  rfl

@[simp] theorem allLt_apply {I : Sort v} (i : I) :
    allLt i = ConvexInequalityRelation.lt :=
  rfl

/-- Interprets one textbook convex-inequality relation between a value and a bound. -/
abbrev holds {γ : Type w} [LE γ] [LT γ] (relation : ConvexInequalityRelation)
    (value μ : γ) : Prop :=
  (relation : LinearConstraintRelation).holds value μ

@[simp] theorem le_holds_iff {γ : Type w} [LE γ] [LT γ] {value μ : γ} :
    (.le : ConvexInequalityRelation).holds value μ ↔ value ≤ μ := by
  simp [holds]

@[simp] theorem lt_holds_iff {γ : Type w} [LE γ] [LT γ] {value μ : γ} :
    (.lt : ConvexInequalityRelation).holds value μ ↔ value < μ := by
  simp [holds]

/-- The owner subset cut out by one convex inequality with the given relation kind. -/
abbrev solutionSet {γ : Type w} [LE γ] [LT γ] (relation : ConvexInequalityRelation)
    (f : E → γ) (μ : γ) : Set E :=
  (relation : LinearConstraintRelation).solutionSet f μ

@[simp] theorem mem_solutionSet_iff {γ : Type w} [LE γ] [LT γ]
    (relation : ConvexInequalityRelation)
    (f : E → γ) (μ : γ) (x : E) :
    x ∈ relation.solutionSet f μ ↔ relation.holds (f x) μ := by
  cases relation <;> rfl

section

variable {𝕜 : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

theorem convex_solutionSet_le {f : E → WithTopBot α}
    (hf : f.IsConvex 𝕜) (μ : WithTopBot α) :
    Convex 𝕜 ((.le : ConvexInequalityRelation).solutionSet f μ) := by
  simpa [solutionSet] using hf.convex_le μ

end

section

variable {𝕜 : Type v}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

theorem convex_solutionSet_lt {f : E → WithTopBot α}
    (hf : f.IsConvex 𝕜) (μ : WithTopBot α) :
    Convex 𝕜 ((.lt : ConvexInequalityRelation).solutionSet f μ) := by
  simpa [solutionSet] using hf.convex_lt μ

theorem convex_solutionSet
    (relation : ConvexInequalityRelation) {f : E → WithTopBot α}
    (hf : f.IsConvex 𝕜) (μ : WithTopBot α) :
    Convex 𝕜 (relation.solutionSet f μ) := by
  cases relation
  · simpa using convex_solutionSet_le (𝕜 := 𝕜) (E := E) (α := α) hf μ
  · simpa using convex_solutionSet_lt (𝕜 := 𝕜) (E := E) (α := α) hf μ

end

end ConvexInequalityRelation

/-- Text 21.0.1 owner layer: the feasible set of a mixed weak/strict inequality system is attached
to an indexed family of bounds `μᵢ` and functions `fᵢ`, each tagged by relation kind. The convex
chapter specializes this owner to `WithTopBot α` codomains. -/
abbrev convexInequalitySolutionSet {I : Sort v} {β : Type w} [LE β] [LT β]
    (relation : I → ConvexInequalityRelation)
    (f : I → E → β) (μ : I → β) : Set E :=
  LinearConstraintRelation.feasibleSet
    (fun i ↦ (relation i : LinearConstraintRelation)) f μ

@[simp] theorem mem_convexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LE β] [LT β]
    {relation : I → ConvexInequalityRelation}
    {f : I → E → β} {μ : I → β} {x : E} :
    x ∈ convexInequalitySolutionSet relation f μ ↔
      ∀ i, (relation i).holds (f i x) (μ i) := by
  simp [convexInequalitySolutionSet, ConvexInequalityRelation.holds]

/-- Chapter 21 weak owner: the feasible set of a weak inequality family `f i x ≤ 0`. -/
abbrev weakConvexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LE β] [Zero β]
    (f : I → E → β) : Set E :=
  LinearConstraintRelation.leFeasible f (fun _ : I ↦ (0 : β))

/-- Membership in the weak Chapter 21 feasible set is pointwise weak feasibility. -/
@[simp] theorem mem_weakConvexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LE β] [Zero β]
    {f : I → E → β} {x : E} :
    x ∈ weakConvexInequalitySolutionSet f ↔ ∀ i : I, f i x ≤ 0 := by
  simp [weakConvexInequalitySolutionSet]

/-- The weak Chapter 21 owner is the all-weak specialization of the mixed owner with zero bounds. -/
@[simp] theorem weakConvexInequalitySolutionSet_eq_convexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LE β] [LT β] [Zero β]
    (f : I → E → β) :
    weakConvexInequalitySolutionSet f =
      convexInequalitySolutionSet ConvexInequalityRelation.allLe f
        (fun _ : I ↦ (0 : β)) := by
  simp [weakConvexInequalitySolutionSet, convexInequalitySolutionSet]

/-- Chapter 21 strict owner: the feasible set of a strict inequality family `f i x < 0`,
presented at the primitive order layer `[LT β]` with zero bounds. -/
abbrev strictConvexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LT β] [Zero β]
    (f : I → E → β) : Set E :=
  LinearConstraintRelation.ltFeasible f (fun _ : I ↦ (0 : β))

/-- Membership in the strict Chapter 21 feasible set is pointwise strict feasibility. -/
@[simp] theorem mem_strictConvexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LT β] [Zero β]
    {f : I → E → β} {x : E} :
    x ∈ strictConvexInequalitySolutionSet f ↔ ∀ i : I, f i x < 0 := by
  simp [strictConvexInequalitySolutionSet]

/-- Where a weak order is available, the strict owner is exactly the all-strict specialization
of `convexInequalitySolutionSet` with zero bounds. -/
@[simp] theorem strictConvexInequalitySolutionSet_eq_convexInequalitySolutionSet
    {I : Sort v} {β : Type w} [LE β] [LT β] [Zero β]
    (f : I → E → β) :
    strictConvexInequalitySolutionSet f =
      convexInequalitySolutionSet ConvexInequalityRelation.allLt f
        (fun _ : I ↦ (0 : β)) := by
  ext x
  simp [strictConvexInequalitySolutionSet, convexInequalitySolutionSet]

/-- Finite-subsystem owner: the feasible set cut out by only the constraints indexed by
`J`. This keeps finite-subsystem surfaces at the canonical feasible-set owner layer instead of
repeating subtype-restriction scaffolding at call sites. -/
abbrev convexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LE β] [LT β] (J : Finset I)
    (relation : I → ConvexInequalityRelation)
    (f : I → E → β) (μ : I → β) : Set E :=
  convexInequalitySolutionSet
    (fun i : J ↦ relation i)
    (fun i : J ↦ f i)
    (fun i : J ↦ μ i)

@[simp] theorem mem_convexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LE β] [LT β] {J : Finset I}
    {relation : I → ConvexInequalityRelation}
    {f : I → E → β} {μ : I → β} {x : E} :
    x ∈ convexInequalitySolutionSetOn J relation f μ ↔
      ∀ i ∈ J, (relation i).holds (f i x) (μ i) := by
  constructor
  · intro hx i hi
    exact (mem_convexInequalitySolutionSet.mp hx) ⟨i, hi⟩
  · intro hx
    exact mem_convexInequalitySolutionSet.mpr (fun i ↦ hx i i.2)

/-- Chapter 21 owner for finite weak convex inequalities with zero right-hand-side bounds. -/
abbrev weakConvexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LE β] [Zero β] (J : Finset I)
    (f : I → E → β) : Set E :=
  LinearConstraintRelation.leFeasible
    (fun i : J ↦ f i) (fun _ : J ↦ (0 : β))

/-- Membership in the finite weak Chapter 21 feasible set is exactly pointwise weak feasibility
on the chosen subsystem. -/
@[simp] theorem mem_weakConvexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LE β] [Zero β] {J : Finset I}
    {f : I → E → β} {x : E} :
    x ∈ weakConvexInequalitySolutionSetOn J f ↔ ∀ i ∈ J, f i x ≤ 0 := by
  constructor
  · intro hx i hi
    exact
      (LinearConstraintRelation.mem_leFeasible
        (b := fun j : J ↦ f j) (β := fun _ : J ↦ (0 : β)) x).1 hx ⟨i, hi⟩
  · intro hx
    exact
      (LinearConstraintRelation.mem_leFeasible
        (b := fun j : J ↦ f j) (β := fun _ : J ↦ (0 : β)) x).2
        (fun j ↦ hx j j.2)

/-- The finite weak feasible-set owner is exactly the textbook finite-conjunction set-builder
view. -/
theorem weakConvexInequalitySolutionSetOn_eq_setOf
    {I : Type v} {β : Type w} [LE β] [Zero β] (J : Finset I)
    (f : I → E → β) :
    weakConvexInequalitySolutionSetOn J f = {x : E | ∀ i ∈ J, f i x ≤ 0} := by
  ext x
  simp

/-- The finite weak Chapter 21 owner is the all-weak specialization of the mixed finite owner
with zero bounds. -/
@[simp] theorem weakConvexInequalitySolutionSetOn_eq_convexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LE β] [LT β] [Zero β] (J : Finset I)
    (f : I → E → β) :
    weakConvexInequalitySolutionSetOn J f =
      convexInequalitySolutionSetOn J ConvexInequalityRelation.allLe f
        (fun _ ↦ (0 : β)) := by
  simp [weakConvexInequalitySolutionSetOn, convexInequalitySolutionSetOn,
    convexInequalitySolutionSet]

/-- Chapter 21 owner for finite strict convex inequalities with zero right-hand-side bounds,
presented at the primitive order layer `[LT β]`. -/
abbrev strictConvexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LT β] [Zero β] (J : Finset I)
    (f : I → E → β) : Set E :=
  LinearConstraintRelation.ltFeasible
    (fun i : J ↦ f i) (fun _ : J ↦ (0 : β))

/-- Membership in the finite strict Chapter 21 feasible set is exactly pointwise strict
feasibility on the chosen subsystem. -/
@[simp] theorem mem_strictConvexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LT β] [Zero β] {J : Finset I}
    {f : I → E → β} {x : E} :
    x ∈ strictConvexInequalitySolutionSetOn J f ↔ ∀ i ∈ J, f i x < 0 := by
  constructor
  · intro hx i hi
    exact
      (LinearConstraintRelation.mem_ltFeasible
        (b := fun j : J ↦ f j) (β := fun _ : J ↦ (0 : β)) x).1 hx ⟨i, hi⟩
  · intro hx
    exact
      (LinearConstraintRelation.mem_ltFeasible
        (b := fun j : J ↦ f j) (β := fun _ : J ↦ (0 : β)) x).2
        (fun j ↦ hx j j.2)

/-- Where a weak order is available, the finite strict owner is exactly the all-strict
specialization of the mixed finite owner with zero bounds. -/
@[simp] theorem strictConvexInequalitySolutionSetOn_eq_convexInequalitySolutionSetOn
    {I : Type v} {β : Type w} [LE β] [LT β] [Zero β] (J : Finset I)
    (f : I → E → β) :
    strictConvexInequalitySolutionSetOn J f =
      convexInequalitySolutionSetOn J ConvexInequalityRelation.allLt f
        (fun _ ↦ (0 : β)) := by
  ext x
  simp [strictConvexInequalitySolutionSetOn, convexInequalitySolutionSetOn,
    convexInequalitySolutionSet]

/- The owner feasible set is exactly the textbook set of points satisfying each indexed weak or
strict convex inequality. -/
theorem convexInequalitySolutionSet_eq_setOf {I : Sort v}
    {β : Type w} [LE β] [LT β] (relation : I → ConvexInequalityRelation)
    (f : I → E → β) (μ : I → β) :
    convexInequalitySolutionSet relation f μ =
      {x : E | ∀ i, (relation i).holds (f i x) (μ i)} := by
  ext x
  simp

section

variable {I : Type v}
variable {𝕜 : Type*}
variable [Fintype I] [LinearOrderedRing 𝕜]

namespace Function

/-- A nonnegative nontrivial multiplier family whose weighted sum is pointwise nonnegative on `C`
with zero lower bound. This is the canonical Chapter 21 certificate owner used by Theorems 21.1
and 21.2. -/
abbrev IsNonnegativeZeroBoundCertificateOn
    (w : I → 𝕜) (C : Set E) (f : I → E → WithTopBot 𝕜) : Prop :=
  (∀ i, 0 ≤ w i) ∧
    w ≠ 0 ∧
      ∀ x : C, (0 : WithTopBot 𝕜) ≤ ∑ i, (w i : WithTopBot 𝕜) * f i x

/-- Whole-space specialization of `IsNonnegativeZeroBoundCertificateOn`. -/
abbrev IsNonnegativeZeroBoundCertificate
    (w : I → 𝕜) (f : I → E → WithTopBot 𝕜) : Prop :=
  w.IsNonnegativeZeroBoundCertificateOn (Set.univ : Set E) f

/-- Pointwise bridge for the whole-space zero-bound certificate owner. -/
@[simp] theorem isNonnegativeZeroBoundCertificate_iff
    {w : I → 𝕜} {f : I → E → WithTopBot 𝕜} :
    w.IsNonnegativeZeroBoundCertificate f ↔
      (∀ i, 0 ≤ w i) ∧
        w ≠ 0 ∧
          ∀ x : E, (0 : WithTopBot 𝕜) ≤ ∑ i, (w i : WithTopBot 𝕜) * f i x := by
  constructor
  · rintro ⟨hnonneg, hne, hsum⟩
    refine ⟨hnonneg, hne, ?_⟩
    intro x
    simpa using hsum ⟨x, Set.mem_univ x⟩
  · rintro ⟨hnonneg, hne, hsum⟩
    refine ⟨hnonneg, hne, ?_⟩
    intro x
    simpa using hsum x

end Function

end

end

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

/-- The all-weak feasible set is convex as soon as every constraint function is convex; this
owner-level form keeps the weak-only API at the weaker order layer used by closed sublevels. -/
theorem convex_weakConvexInequalitySolutionSet {I : Sort v}
    (f : I → E → WithTopBot α) (hf : ∀ i, (f i).IsConvex 𝕜) :
    Convex 𝕜 (weakConvexInequalitySolutionSet f) := by
  have hconv :
      Convex 𝕜 {x : E | ∀ i : I, f i x ≤ (0 : WithTopBot α)} := by
    simpa using convex_iInter (fun i : I ↦ (hf i).convex_le (0 : WithTopBot α))
  simpa [weakConvexInequalitySolutionSet, LinearConstraintRelation.leFeasible_eq_setOf] using
    hconv

/-- The finite all-weak feasible set on a chosen subsystem is convex under convexity of each
constraint. -/
theorem convex_weakConvexInequalitySolutionSetOn
    {I : Type v} (J : Finset I) (f : I → E → WithTopBot α)
    (hf : ∀ i, (f i).IsConvex 𝕜) :
    Convex 𝕜 (weakConvexInequalitySolutionSetOn J f) := by
  simpa [weakConvexInequalitySolutionSetOn] using
    convex_weakConvexInequalitySolutionSet
      (𝕜 := 𝕜) (E := E) (α := α)
      (I := J) (f := fun i : J ↦ f i) (hf := fun i ↦ hf i)

end

section

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

/-- Each indexed weak or strict convex inequality cuts out a convex set, so their common feasible
set is convex as soon as every left-hand side is convex. -/
theorem convex_convexInequalitySolutionSet {I : Sort v}
    (relation : I → ConvexInequalityRelation)
    (f : I → E → WithTopBot α) (μ : I → WithTopBot α)
    (hf : ∀ i, (f i).IsConvex 𝕜) :
    Convex 𝕜 (convexInequalitySolutionSet relation f μ) := by
  simpa [convexInequalitySolutionSet] using
    convex_iInter fun i ↦ (relation i).convex_solutionSet (hf i) (μ i)

/-- Finite-subsystem owner form of convexity for mixed weak/strict systems. -/
theorem convex_convexInequalitySolutionSetOn
    {I : Type v} (J : Finset I)
    (relation : I → ConvexInequalityRelation)
    (f : I → E → WithTopBot α) (μ : I → WithTopBot α)
    (hf : ∀ i, (f i).IsConvex 𝕜) :
    Convex 𝕜 (convexInequalitySolutionSetOn J relation f μ) := by
  simpa [convexInequalitySolutionSetOn] using
    convex_convexInequalitySolutionSet
      (𝕜 := 𝕜) (E := E) (α := α)
      (relation := fun i : J ↦ relation i)
      (f := fun i : J ↦ f i)
      (μ := fun i : J ↦ μ i)
      (hf := fun i ↦ hf i)

end
