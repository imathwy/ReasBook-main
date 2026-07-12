import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_9_1_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Pointwise Rockafellar

section NoOppositeRecessionDirections

variable {𝕜 : Type*} [Zero 𝕜] [LE 𝕜]
variable {E : Type*} [Zero E] [Add E] [Neg E] [SMul 𝕜 E]

namespace Set

/-- Binary opposite-recession exclusion condition used in Corollary 9.1.2:
no nonzero direction is simultaneously a recession direction of `C₁` and the opposite of a
recession direction of `C₂`. -/
def NoOppositeRecessionDirections (𝕜 : Type*) [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E]
    (C₁ C₂ : Set E) : Prop :=
  ∀ ⦃y : E⦄, y ∈ 0⁺[𝕜] C₁ → -y ∈ 0⁺[𝕜] C₂ → y = 0

end Set

scoped[Rockafellar] notation:50 C₁ " ⟂₀⁺[" 𝕜 "] " C₂ =>
  Set.NoOppositeRecessionDirections 𝕜 C₁ C₂

end NoOppositeRecessionDirections

section

open Set

variable
  {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
  {E : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 9.1.2 is the binary (`m = 2`) specialization of Corollary 9.1.1:
  closedness of the Minkowski sum and the recession-cone identity for the Minkowski sum
  of two closed convex subsets of a finite-dimensional Hausdorff topological vector space over
  `𝕜`, together with the
  corresponding recession-cone formula. The source states this in `ℝ^n`, but the owner theorem
  already lives intrinsically and the present binary specialization uses no coordinate data.
- `core/canonical`: the owner-side notions already present in the chapter are the recession-cone
  owner `0⁺[𝕜]C` and lineality-space owner `lin[𝕜](C)`.
- `bridge/view`: the textbook phrase "there is no direction of recession of `C₁` whose opposite is
  a direction of recession of `C₂`" is rendered on the owner surface as
  `y ∈ 0⁺[𝕜]C₁ → -y ∈ 0⁺[𝕜]C₂ → y = 0`.

Domain-style sampling used here:
- the finite-family owner theorems
  `Set.ZeroSumRecessionImpLineality.isClosed_sum` and
  `Set.ZeroSumRecessionImpLineality.recessionCone_closure_sum_eq_sum_recessionCone_closure`
  from Corollary 9.1.1;
- the chapter owner `recessionCone` from Definition 8.0.2;
- the chapter owner `Set.linealitySpace` from Definition 8.4.2.

Primitive data vs derived API:
- primitive inputs: the two sets `C₁`, `C₂`, their convexity, and the owner-layer compatibility
  condition on closure recession directions
  `y ∈ 0⁺[𝕜](closure C₁) → -y ∈ 0⁺[𝕜](closure C₂) → y = 0`;
- derived source-facing outputs for this corollary: the closed-set statement
  `IsClosed (C₁ + C₂)` and the closed-set recession-cone identity
  `0⁺[𝕜] (C₁ + C₂) = 0⁺[𝕜]C₁ + 0⁺[𝕜]C₂`.
  The finite-sum owner theorem already absorbs the empty cases, so nonemptiness is not primitive
  public data here.

Layer target: this item exposes the binary specialization first at the closure owner layer, then
recovers the textbook closed-set surface as a corollary.

Assumption audit for this canonicalization pass:
- `Module 𝕜 E` is retained as a primitive owner-layer assumption: both `Convex 𝕜` and the
  textbook owner notation `0⁺[𝕜]C` are scalar-parameterized at this layer.
- `TopologicalSpace E`, `IsTopologicalAddGroup E`, and `ContinuousSMul 𝕜 E` are primitive for the
  ambient closedness/closure owners (`IsClosed`, `closure`) used by both conclusions.
- `FiniteDimensional 𝕜 E` and `T2Space E` are inherited from the first upstream owner source
  (`Theorem_9_1` via `Corollary_9_1_1`); this file does not introduce extra ambient structure
  beyond that owner layer.
- Topology-language audit: this item's mathematical content is ambient closedness of `C₁ + C₂`
  plus an ambient recession-cone identity. There is no stricter intrinsic/relative reformulation
  available in the local Chapter 9 owner ecosystem that would strictly generalize these two public
  theorem surfaces.
-/

variable {C₁ C₂ : Set E}

private def pairFamily (C₁ C₂ : Set E) : Bool → Set E := fun b ↦ cond b C₁ C₂

local notation "pairSets" => pairFamily C₁ C₂

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E]
  [FiniteDimensional 𝕜 E] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem pairSets_convex (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    ∀ b : Bool, Convex 𝕜 (pairSets b) := by
  intro b
  cases b
  · simpa [pairFamily] using hC₂_convex
  · simpa [pairFamily] using hC₁_convex

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Binary bridge to the canonical finite-family owner:
the no-opposite condition on closure recession directions implies the zero-sum lineality
condition for the `Bool`-indexed pair. -/
theorem Set.NoOppositeRecessionDirections.zeroSumRecessionImpLineality_pair
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂)) :
    Set.ZeroSumRecessionImpLineality 𝕜 pairSets := by
  change (∀ {y : E}, y ∈ 0⁺[𝕜] (closure C₁) → -y ∈ 0⁺[𝕜] (closure C₂) → y = 0) at hNoOppositeClosure
  intro z hz hsum b
  have hz_true : z true ∈ 0⁺[𝕜] (closure C₁) := by
    simpa [pairFamily] using hz true
  have hz_false : z false ∈ 0⁺[𝕜] (closure C₂) := by
    simpa [pairFamily] using hz false
  have hsum' : z true + z false = 0 := by
    simpa [Fintype.sum_bool, add_comm, add_left_comm, add_assoc] using hsum
  have hsum'' : z false + z true = 0 := by
    simpa [add_comm] using hsum'
  have hz_false_neg : -z true ∈ 0⁺[𝕜] (closure C₂) := by
    simpa [eq_neg_of_add_eq_zero_left hsum''] using hz_false
  have hz_true_eq_zero : z true = 0 :=
    hNoOppositeClosure hz_true hz_false_neg
  have hz_false_eq_zero : z false = 0 := by
    simpa [hz_true_eq_zero] using hsum'
  have hzero₁ : (0 : E) ∈ 0⁺[𝕜] (closure C₁) := by
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  have hzero₂ : (0 : E) ∈ 0⁺[𝕜] (closure C₂) := by
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    simpa using hx
  cases b
  · rw [mem_lineal_iff]
    constructor <;> simpa [Set.mem_neg, hz_false_eq_zero] using hzero₂
  · rw [mem_lineal_iff]
    constructor <;> simpa [Set.mem_neg, hz_true_eq_zero] using hzero₁

/-- Binary specialization of Corollary 9.1.1 (1) on the closure-owner layer:
under the closure-level no-opposite condition, the closure of the Minkowski sum equals the
sum of closures. -/
theorem Set.NoOppositeRecessionDirections.closure_add_eq_add_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    closure (C₁ + C₂) = closure C₁ + closure C₂ := by
  have hpairZero :
      Set.ZeroSumRecessionImpLineality 𝕜 pairSets :=
    hNoOppositeClosure.zeroSumRecessionImpLineality_pair
  have hclosure :
      closure (∑ b, pairSets b : Set E) = ∑ b, closure (pairSets b) :=
    hpairZero.closure_sum_eq_sum_closure (pairSets_convex hC₁_convex hC₂_convex)
  simpa [Fintype.sum_bool, pairFamily, add_comm, add_left_comm, add_assoc] using hclosure

omit [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] in
private theorem Set.NoOppositeRecessionDirections.closure_of_isClosed
    (hNoOpposite : C₁ ⟂₀⁺[𝕜] C₂)
    (hC₁_closed : IsClosed C₁) (hC₂_closed : IsClosed C₂) :
    (closure C₁) ⟂₀⁺[𝕜] (closure C₂) := by
  simpa [Set.NoOppositeRecessionDirections, hC₁_closed.closure_eq, hC₂_closed.closure_eq] using
    hNoOpposite

/-- Binary closure-layer specialization of Corollary 9.1.1 (1): if two convex sets satisfy the
closure-level compatibility condition on opposite recession directions, then the sum of their
closures is closed. -/
theorem Set.NoOppositeRecessionDirections.isClosed_add_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    IsClosed (closure C₁ + closure C₂) := by
  simpa [hNoOppositeClosure.closure_add_eq_add_closure hC₁_convex hC₂_convex] using
    (isClosed_closure : IsClosed (closure (C₁ + C₂)))

/-- Binary specialization of Corollary 9.1.1 (2) on the closure-owner layer:
under the same closure-level compatibility condition, the recession cone of the closure of the
Minkowski sum is the sum of the recession cones of the individual closures. -/
theorem Set.NoOppositeRecessionDirections.recessionCone_closure_add_eq_add_recessionCone_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    0⁺[𝕜] (closure (C₁ + C₂)) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) := by
  have hpairZero :
      Set.ZeroSumRecessionImpLineality 𝕜 pairSets :=
    hNoOppositeClosure.zeroSumRecessionImpLineality_pair
  have hcone :
      0⁺[𝕜] (closure (∑ b, pairSets b : Set E)) =
        ∑ b, 0⁺[𝕜] (closure (pairSets b)) :=
    hpairZero.recessionCone_closure_sum_eq_sum_recessionCone_closure
      (pairSets_convex hC₁_convex hC₂_convex)
  simpa [Fintype.sum_bool, pairFamily, add_comm, add_left_comm, add_assoc] using hcone

/-- Binary closure-layer specialization of Corollary 9.1.1 (2): under the same closure-level
compatibility condition, the recession cone of the sum of closures is the sum of the
recession cones of the individual closures. -/
theorem Set.NoOppositeRecessionDirections.recessionCone_add_closure_eq_add_recessionCone_closure
    (hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂))
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂) :
    0⁺[𝕜] (closure C₁ + closure C₂) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) := by
  have hcone_closure_add :
      0⁺[𝕜] (closure (C₁ + C₂)) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) :=
    hNoOppositeClosure.recessionCone_closure_add_eq_add_recessionCone_closure hC₁_convex hC₂_convex
  have hclosure_add : closure (C₁ + C₂) = closure C₁ + closure C₂ :=
    hNoOppositeClosure.closure_add_eq_add_closure hC₁_convex hC₂_convex
  simpa [hclosure_add] using hcone_closure_add

/-- Corollary 9.1.2 (1): if `C₁` and `C₂` are closed convex sets in a finite-dimensional
Hausdorff topological vector space over `𝕜` and every `y` with
`y ∈ 0⁺[𝕜]C₁` and `-y ∈ 0⁺[𝕜]C₂` is zero, then
their Minkowski sum `C₁ + C₂` is closed. In
particular, the hypothesis holds whenever either set is bounded. -/
-- Proof sketch: first transport the source-facing no-opposite condition to the closure owner
-- surface, then apply the closure-layer binary specialization
-- `Set.NoOppositeRecessionDirections.isClosed_add_closure`. Closedness of each summand rewrites
-- this directly to `IsClosed (C₁ + C₂)`.
theorem Set.NoOppositeRecessionDirections.isClosed_add
    (hC₁_closed : IsClosed C₁) (hC₂_closed : IsClosed C₂)
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂)
    (hNoOpposite : C₁ ⟂₀⁺[𝕜] C₂) :
    IsClosed (C₁ + C₂) := by
  have hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂) :=
    hNoOpposite.closure_of_isClosed hC₁_closed hC₂_closed
  simpa [hC₁_closed.closure_eq, hC₂_closed.closure_eq] using
    hNoOppositeClosure.isClosed_add_closure hC₁_convex hC₂_convex

/-- Corollary 9.1.2 (2): under the same hypotheses, the recession cone of the Minkowski sum is the
sum of the recession cones:
`0⁺[𝕜] (C₁ + C₂) = 0⁺[𝕜]C₁ + 0⁺[𝕜]C₂`. -/
-- Proof sketch: apply the closure-layer recession-cone theorem
-- `Set.NoOppositeRecessionDirections.recessionCone_add_closure_eq_add_recessionCone_closure`,
-- then rewrite closures using closedness of both summands and of `C₁ + C₂` from part (1).
theorem Set.NoOppositeRecessionDirections.recessionCone_add_eq_add_recessionCone
    (hC₁_closed : IsClosed C₁) (hC₂_closed : IsClosed C₂)
    (hC₁_convex : Convex 𝕜 C₁) (hC₂_convex : Convex 𝕜 C₂)
    (hNoOpposite : C₁ ⟂₀⁺[𝕜] C₂) :
    0⁺[𝕜] (C₁ + C₂) = 0⁺[𝕜]C₁ + 0⁺[𝕜]C₂ := by
  have hNoOppositeClosure : (closure C₁) ⟂₀⁺[𝕜] (closure C₂) :=
    hNoOpposite.closure_of_isClosed hC₁_closed hC₂_closed
  have hclosed_add : IsClosed (C₁ + C₂) :=
    hNoOpposite.isClosed_add hC₁_closed hC₂_closed hC₁_convex hC₂_convex
  have hcone_closure :
      0⁺[𝕜] (closure C₁ + closure C₂) = 0⁺[𝕜] (closure C₁) + 0⁺[𝕜] (closure C₂) :=
    hNoOppositeClosure.recessionCone_add_closure_eq_add_recessionCone_closure hC₁_convex hC₂_convex
  simpa [hclosed_add.closure_eq, hC₁_closed.closure_eq, hC₂_closed.closure_eq] using hcone_closure

end
