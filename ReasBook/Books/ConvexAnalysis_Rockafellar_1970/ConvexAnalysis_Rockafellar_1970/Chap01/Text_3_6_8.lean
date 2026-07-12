import ConvexAnalysis_Rockafellar_1970.Chap01.Proposition_2_6_12
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_6_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_3_6_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

open scoped Pointwise
open scoped Rockafellar

variable {R : Type*}
variable {E : Type u}

section

variable [Zero R] [LT R]
variable [SMul R E]

set_option quotPrecheck false in
scoped[Rockafellar] notation "K⁺[" R " | " C "]" =>
  ({p : R × E | 0 < p.1 ∧ p.2 ∈ p.1 • C} : Set (R × E))

@[simp] theorem Set.mem_posHomogenizationSet_iff (C : Set E) (p : R × E) :
    p ∈ K⁺[R | C] ↔ 0 < p.1 ∧ p.2 ∈ p.1 • C :=
  Iff.rfl

end

section

variable [Zero R] [Preorder R]
variable [SMul R E]

/-- Under a preorder, `K⁺[R | C]` is exactly the strict-positive-height part of `K[R | C]`. -/
theorem Set.mem_posHomogenizationSet_iff_mem_homogenizationSet_and_pos
    (C : Set E) (p : R × E) :
    p ∈ K⁺[R | C] ↔ p ∈ K[R | C] ∧ 0 < p.1 := by
  rw [Set.mem_posHomogenizationSet_iff, mem_homogenizationSet_iff R C]
  constructor
  · rintro ⟨hp_pos, hp_mem⟩
    exact ⟨⟨le_of_lt hp_pos, hp_mem⟩, hp_pos⟩
  · rintro ⟨hpK, hp_pos⟩
    exact ⟨hp_pos, hpK.2⟩

end

section

variable [Zero R] [One R] [Add R] [LT R]
variable [SMul R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.8 fixes convex sets `C₁, C₂ ⊆ R^n`, forms their homogenization sets
  `K₁ = homogenizationSet C₁` and `K₂ = homogenizationSet C₂`, then defines `K` as the set of
  pairs `(λ, x)` for which the first coordinate decomposes as `λ = λ₁ + λ₂` with
  `0 < λ₁`, `0 < λ₂`, `(λ₁, x) ∈ K₁`, and `(λ₂, x) ∈ K₂`.
- `core/canonical`: the owner abstractions used here are `homogenizationSet`,
  the first-coordinate fiberwise-sum owner `+ᶠ₁`, and `inverseAddition`.
- `bridge/view`: the theorem is the direct coefficient comparison between the unit slice of the
  first-coordinate fiberwise sum of the positivity-filtered homogenization sets and the owner
  operation `inverseAddition C₁ C₂` from Text 3.6.1.
- Primitive data vs derived API: the primitive strict surface here is the direct notation
  `K⁺[R | C] = {p | 0 < p.1 ∧ p.2 ∈ p.1 • C}`, while the connection to
  `K[R | C] ∩ {p | 0 < p.1}` is a bridge theorem valid under a preorder.
- Domain-style sampling: this statement reuses `Set.mem_fiberwiseFirstSum_mk_iff`,
  `inverseAddition`, and `Set.mem_inverseAddition_primitive_iff`.
- Ambient minimization: both public theorems use only the pointwise scalar action on `E`,
  together with additive height arithmetic on `R` (`0`, `1`, `+`, `<`), so
  the file should live over the same scalar-action owner layer as `inverseAddition` rather than
  over unnecessary multiplicative ring structure on the scalar side.
-/

/-- Membership in the unit slice from Text 3.6.8 is equivalent to membership in the inverse
addition `C₁ #[R] C₂`, in its primitive two-coefficient owner form. -/
-- Proof sketch: rewrite the first-coordinate fiberwise sum using
-- `Set.mem_fiberwiseFirstSum_mk_iff`, then rewrite inverse addition via
-- `Set.mem_inverseAddition_primitive_iff`.
@[simp] theorem
    mem_unitSection_fiberwiseFirstSum_pos_homogenizationSet_iff
    (C₁ C₂ : Set E) (x : E) :
    x ∈ U[R | (K⁺[R | C₁] +ᶠ₁ K⁺[R | C₂])] ↔
      x ∈ C₁ #[R] C₂ := by
  rw [mem_unitSection_iff, Set.mem_fiberwiseFirstSum_mk_iff, Set.mem_inverseAddition_primitive_iff]
  constructor
  · rintro ⟨a₁, a₂, ha₁, ha₂, hsum⟩
    exact ⟨a₁, a₂, ha₁.1, ha₂.1, hsum, ⟨ha₁.2, ha₂.2⟩⟩
  · rintro ⟨a₁, a₂, ha₁_pos, ha₂_pos, hsum, hx⟩
    exact ⟨a₁, a₂, ⟨ha₁_pos, hx.1⟩, ⟨ha₂_pos, hx.2⟩, hsum⟩

/-- Text 3.6.8: if `K₁` and `K₂` are the homogenization sets of `C₁` and `C₂`, then the unit slice
of the first-coordinate fiberwise sum of their strict-positive-height parts is exactly the
inverse addition `C₁ #[R] C₂`. This statement is valid for arbitrary subsets, so the convex case
from the text is immediate. -/
theorem unitSection_fiberwiseFirstSum_pos_homogenizationSet_eq_inverseAddition
    (C₁ C₂ : Set E) :
    U[R | (K⁺[R | C₁] +ᶠ₁ K⁺[R | C₂])] = C₁ #[R] C₂ := by
  ext x
  simpa using
    (mem_unitSection_fiberwiseFirstSum_pos_homogenizationSet_iff C₁ C₂ x)

end

end
