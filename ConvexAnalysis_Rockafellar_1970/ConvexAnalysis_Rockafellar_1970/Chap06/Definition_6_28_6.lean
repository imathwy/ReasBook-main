import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_28_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u w

noncomputable section

namespace OrdinaryConvexProgram
open scoped Rockafellar

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.28.6 introduces the multiplier set `E_r`.
- `core/canonical`: the Lagrangian owner for an ordinary convex program is already
  `OrdinaryConvexProgram.saddleLagrangian` from `Definition_6_28_3`, together with the existing
  weighted-objective owner `weightedObjective`.
- `bridge/view`: the textbook multiplier vector is represented canonically here by a pair of
  coordinate blocks `((ι → β) × τ)`, so that only the first block carries the nonnegativity
  condition defining `E_r`; the second block is unrestricted and specializes to the equality
  multiplier block `(κ → β)` in the program-facing lemmas below. The source piecewise formula is
  then restated by branch lemmas for the existing Lagrangian owner.

Domain-style sampling used here:
- `OrdinaryConvexProgram.saddleLagrangian` from `Chap06.Definition_6_28_3`;
- `OrdinaryConvexProgram.weightedObjective` from `Chap06.Definition_6_28_3`;
- `OrdinaryConvexProgram.weightedObjective_of_mem_constraintSet` from
  `Chap06.Definition_6_28_3`;
- the canonical order interval owner `Set.Ici` on the inequality-multiplier block `ι → β`,
  combined with an unrestricted companion block.

Primitive data vs derived API:
- primitive source-facing data: the multiplier set `multiplierSet`;
- core owner reused from upstream: `P.saddleLagrangian`;
- derived API: coordinatewise membership in the multiplier set and the three pointwise branch
  formulas for `P.saddleLagrangian`.

Layer target: `source-facing` for `multiplierSet`, and `bridge/view` for the branch lemmas that
restate the source formula on the existing Lagrangian owner.
-/

section MultiplierSet

variable {β : Type w} [Zero β] [Preorder β]
variable {ι τ : Type*}

/-- The multiplier set attached to an ordinary convex program: the inequality multipliers are
coordinatewise nonnegative, while the companion multiplier block is unrestricted. -/
def multiplierSet : Set ((ι → β) × τ) :=
  Set.Ici (0 : ι → β) ×ˢ Set.univ

scoped[Rockafellar] notation "Eᵣ" => multiplierSet

-- Proof sketch: unfold `multiplierSet`; membership in the defining set-builder is exactly the
-- coordinatewise nonnegativity condition on the inequality multiplier block.
/-- Coordinatewise characterization of the multiplier set of an ordinary convex program. -/
@[simp] theorem mem_multiplierSet (u : (ι → β) × τ) :
    u ∈ Eᵣ ↔ ∀ i, 0 ≤ u.1 i := by
  simp [multiplierSet]
  rfl

end MultiplierSet

section SaddleLagrangian

variable {𝕜 : Type w} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]
variable {β : Type*} [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β] [Top β] [Bot β]
variable {r s : ℕ} {ι κ : Type}
variable [Fintype ι] [Fintype κ]
variable [Fact (Fintype.card ι = r)] [Fact (Fintype.card κ = s)]
variable (P : OrdinaryConvexProgram 𝕜 E β r s ι κ)

-- Proof sketch: `u ∈ multiplierSet` is exactly the nonnegativity branch used by
-- `P.saddleLagrangian`, so admissible multipliers force the weighted-objective branch globally.
/-- Admissible multipliers give the weighted-objective branch of `P.saddleLagrangian`. -/
theorem saddleLagrangian_apply_of_mem_multiplierSet
    {u : (ι → 𝕜) × (κ → 𝕜)} {x : E}
    (hu : u ∈ Eᵣ) :
    P.saddleLagrangian u x = P.weightedObjective u.1 u.2 x := by
  have hnonneg : ∀ i, 0 ≤ u.1 i := by simpa using hu
  simp [saddleLagrangian, hnonneg]

-- Proof sketch: `u ∉ multiplierSet` means the nonnegativity branch of
-- `P.saddleLagrangian` is unavailable; on `P.constraintSet` the remaining branch is `⊥`.
/-- On the constraint set, inadmissible multipliers make `P.saddleLagrangian` equal to `⊥`. -/
theorem saddleLagrangian_apply_of_mem_constraintSet_of_not_mem_multiplierSet
    {u : (ι → 𝕜) × (κ → 𝕜)} {x : E}
    (hx : x ∈ P.constraintSet) (hu : u ∉ Eᵣ) :
    P.saddleLagrangian u x = ⊥ := by
  have hnonneg : ¬ ∀ i, 0 ≤ u.1 i := by simpa using hu
  simp [saddleLagrangian, hnonneg, hx]

-- Proof sketch: off `P.constraintSet`, the extension branch of `P.saddleLagrangian` is `⊤` when
-- the multipliers are admissible, and the fallback branch is also `⊤` when they are not.
/-- Off the constraint set, `P.saddleLagrangian` is `⊤`. -/
theorem saddleLagrangian_apply_of_not_mem_constraintSet
    {u : (ι → 𝕜) × (κ → 𝕜)} {x : E}
    (hx : x ∉ P.constraintSet) :
    P.saddleLagrangian u x = ⊤ := by
  by_cases hu : u ∈ Eᵣ
  · have hnonneg : ∀ i, 0 ≤ u.1 i := by simpa using hu
    simpa [saddleLagrangian, hnonneg] using
      (P.weightedObjective_of_notMem_constraintSet u.1 u.2 hx)
  · have hnonneg : ¬ ∀ i, 0 ≤ u.1 i := by simpa using hu
    simp [saddleLagrangian, hnonneg, hx]

end SaddleLagrangian

end OrdinaryConvexProgram
