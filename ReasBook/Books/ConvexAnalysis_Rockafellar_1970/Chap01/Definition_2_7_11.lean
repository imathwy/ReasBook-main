import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

variable {R : Type w} [Preorder R]
variable {M : Type u} {N : Type v}
variable [HasPairing M N R]

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Definition 2.7.11 introduces the barrier cone of a subset as the set of
  vectors `x*` such that the values `⟪x, x*⟫` are bounded above on that subset.
- `core/canonical`: the primitive owner abstraction is the set-level barrier cone
  `barrierCone C : Set N`.
- `bridge/view`: `mem_barrier_iff_exists_bound` rewrites membership into the textbook
  quantifier form with
  an explicit bound `β : R`.
- Primitive data vs derived API: the source-facing owner is `barrierCone C`; the explicit-bound
  formulation is derived API through membership.
- Ambient structure: the source-facing owner uses only a pairing and order on the codomain.
- Domain-style sampling: the relevant owner/style declarations in this domain are `BddAbove`,
  `bddAbove_def`, and the adjacent owner `normalCone`.
-/

variable (R)
/-- Definition 2.7.11 (primitive owner): the barrier predicate of `C`, i.e. the set of vectors
`x*` for which the pairing image `{⟪x, x*⟫ | x ∈ C}` is bounded above. -/
def barrierCone (C : Set M) : Set N :=
  {xStar | BddAbove ((fun x : M ↦ (⟪x, xStar⟫ₚ : R)) '' C)}

end

/-- Canonical barrier-cone notation with explicit codomain parameter; the carrier is inferred from
surrounding terms. -/
scoped[Rockafellar] notation3:max "barr[" R "](" C ")" => (@barrierCone R _ _ _ _ C)

section

universe u v w

variable {R : Type w} [Preorder R]
variable {M : Type u} {N : Type v}
variable [HasPairing M N R]

open scoped Rockafellar

/-- Membership in the set-level barrier owner is exactly bounded-above pairing image. -/
@[simp] theorem mem_barrier_iff {C : Set M} {xStar : N} :
    xStar ∈ barr[R](C) ↔
      BddAbove ((fun x : M ↦ (⟪x, xStar⟫ₚ : R)) '' C) := by
  rfl

/-- Membership in `barr[R](C)` is exactly the textbook boundedness condition with an explicit
upper bound. -/
theorem mem_barrier_iff_exists_bound {C : Set M} {xStar : N} :
    xStar ∈ barr[R](C) ↔ ∃ β : R, ∀ x ∈ C, ⟪x, xStar⟫ₚ ≤ β := by
  rw [mem_barrier_iff]
  rw [bddAbove_def]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨β, fun x hx ↦ hβ _ ⟨x, hx, rfl⟩⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β, fun _ hx ↦ by rcases hx with ⟨x, hxC, rfl⟩; exact hβ x hxC⟩

end
