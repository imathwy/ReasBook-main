import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise
open scoped Rockafellar

universe u v

section OrderedPositiveCone

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.1 says the order-upper closure of a convex set remains convex.
- `core/canonical`: the owner data are `upperClosure`, `mem_upperClosure`, and the positive-cone
  owner `orthant[R](E)` in an ordered additive module.
- `bridge/view`: the set-builder surface `{x | ∃ x₁ ∈ C, x ≥ x₁}` is a thin restatement of
  `upperClosure C`.
- Primitive data vs derived API: convexity of `C` is primitive; the Minkowski-sum and set-builder
  views are bridge restatements of the owner statement on `upperClosure C`.
- Layer target: `core/canonical`.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no extended-value codomain appears; no codomain lift is needed.
- Scalar/ambient check: the raw upper-closure/Minkowski identity is scalar-free; we expose a
  primitive noncommutative ordered-group statement first (`Set.Ici 0 + C`) and keep the
  commutative orientation (`C + Set.Ici 0`) as a bridge theorem.
- Owner check: keep `orthant[R](E)` as the chapter bridge owner, derived from the primitive
  `Set.Ici (0 : E)` layer.
- Topology check: this source item is not topology-facing.
- Notation check: reuse existing owners/notation (`upperClosure`, `orthant[𝕜](M)`); no new notation
  layer is introduced.
-/

/-- Helper for Text 3.1.1: at the weakest ordered-additive layer, the upper closure is the left
Minkowski sum with `Set.Ici 0`. -/
theorem upperClosure_eq_Ici_add
    {E : Type u} [AddGroup E] [Preorder E] [AddRightMono E]
    (C : Set E) :
    {x : E | x ∈ upperClosure C} = Set.Ici (0 : E) + C := by
  ext x
  constructor
  · rintro ⟨x₁, hx₁, hx₁x⟩
    -- Rewrite an upper-closure witness as a sum of a nonnegative displacement and a base point.
    refine ⟨x - x₁, sub_nonneg.mpr hx₁x, x₁, hx₁, by simp⟩
  · rintro ⟨z, hz, x₁, hx₁, rfl⟩
    -- A point in `Set.Ici 0 + C` dominates its `C`-component.
    refine ⟨x₁, hx₁, ?_⟩
    simpa using add_le_add_left (show (0 : E) ≤ z from hz) x₁

/-- Helper for Text 3.1.1: in the commutative setting, the upper closure is the right Minkowski
sum with `Set.Ici 0`. -/
theorem upperClosure_eq_add_Ici
    {E : Type u} [AddCommGroup E] [Preorder E] [AddRightMono E]
    (C : Set E) :
    {x : E | x ∈ upperClosure C} = C + Set.Ici (0 : E) := by
  -- Commute the primitive Minkowski-sum presentation into the textbook orientation.
  simpa [add_comm] using (upperClosure_eq_Ici_add (C := C))

/-- Helper for Text 3.1.1: in an ordered additive module, the upper closure is the Minkowski sum
with the nonnegative orthant. -/
theorem upperClosure_eq_add_orthant
    {R : Type v} [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] [Module R E] [PosSMulMono R E]
    (C : Set E) :
    {x : E | x ∈ upperClosure C} = C + orthant[R](E) := by
  -- Replace `Set.Ici 0` with the chapter's orthant owner.
  simpa [orthant_eq_Ici] using
    (upperClosure_eq_add_Ici C)

/-- Helper for Text 3.1.1: the upper closure of a convex set is convex at the owner level. -/
theorem Convex.upperClosure
    {R : Type v} [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommMonoid E] [Preorder E]
    [IsOrderedAddMonoid E] [SMul R E] [PosSMulMono R E]
    {C : Set E} (hC : Convex R C) :
    Convex R {x : E | x ∈ upperClosure C} := by
  intro x hx y hy a b ha hb hab
  rcases (mem_upperClosure.mp hx) with ⟨x₁, hx₁, hx₁x⟩
  rcases (mem_upperClosure.mp hy) with ⟨y₁, hy₁, hy₁y⟩
  -- Combine the original witnesses using convexity inside `C`.
  refine mem_upperClosure.mpr ?_
  refine ⟨a • x₁ + b • y₁, hC hx₁ hy₁ ha hb hab, ?_⟩
  -- Monotonicity of positive scalar multiplication preserves the witness inequalities.
  exact add_le_add (smul_le_smul_of_nonneg_left hx₁x ha)
    (smul_le_smul_of_nonneg_left hy₁y hb)

/-- Text 3.1.1: the order-upper closure of a convex set is convex. -/
theorem convex_setOf_exists_mem_ge
    {R : Type v} [Semiring R] [PartialOrder R]
    {E : Type u} [AddCommMonoid E] [Preorder E]
    [IsOrderedAddMonoid E] [SMul R E] [PosSMulMono R E]
    (C : Set E) (hC : Convex R C) :
    Convex R {x : E | ∃ x₁ ∈ C, x ≥ x₁} := by
  -- Move to the owner theorem on `upperClosure`.
  have hUpper : Convex R {x : E | x ∈ upperClosure C} := hC.upperClosure
  -- Translate back to the textbook set-builder surface.
  simpa [mem_upperClosure, ge_iff_le] using hUpper

end OrderedPositiveCone
