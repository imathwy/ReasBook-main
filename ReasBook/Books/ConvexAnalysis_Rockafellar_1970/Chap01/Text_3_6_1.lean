import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Pointwise
open Set

section

variable (R : Type*)
variable [Zero R] [One R] [Add R] [LT R]
variable {E : Type u}
variable [SMul R E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.6.1 describes inverse addition by strict positive coefficients whose
  sum is `1`, equivalently by the one-parameter surface
  `(1 - λ) • C₁ ∩ λ • C₂` for `0 < λ < 1`.
- `core/canonical`: the owner abstraction is `Set E` with pointwise scalar action,
  strict positivity on two coefficients `t₁,t₂`, and the primitive normalization
  equation `t₁ + t₂ = 1`.
- `bridge/view`: the one-parameter textbook form is a derived bridge obtained by writing
  `t₂ = λ` and `t₁ = 1 - λ`; this bridge belongs at theorem level rather than in the owner.
- Primitive data vs derived API: the subsets and normalized coefficients are primitive data;
  one-parameter `(1 - t, t)` statements are derived API.
- Domain-style sampling: this aligns with pointwise scalar-action owners on sets and the
  strict-coefficient normalization patterns used in neighboring chapter bridge files.
- Ambient minimization: the owner only needs
  `[Zero R] [One R] [Add R] [LT R] [SMul R E]`.
- Layer target: `source-facing`; this file owns the operation and a minimal bridge theorem.
- Abstraction audit (canonicalize):
  - Codomain/ambient layer over-concrete? `No`: owner is intrinsic on `Set E`.
  - Scalar/ambient structure over-concrete? `No`: owner keeps only additive/ordered scalar data
    used by strict-coefficient normalization.
  - Owner tied to a concrete model? `No`: no Euclidean/coordinate owner is used.
  - Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topological statement here.
  - Owner/notation surface too heavy? `No`: short owner `Set.inverseAddition` and textbook
    notation `#[R]` are both present and used on theorem surfaces.
-/

/-- Text 3.6.1: inverse addition `C₁ # C₂` consists of points in `t₁ • C₁ ∩ t₂ • C₂`
for some strict positive coefficients `t₁,t₂` with `t₁ + t₂ = 1`. -/
def Set.inverseAddition (C₁ C₂ : Set E) : Set E :=
  {x | ∃ t₁ t₂, 0 < t₁ ∧ 0 < t₂ ∧ t₁ + t₂ = (1 : R) ∧ x ∈ t₁ • C₁ ∩ t₂ • C₂}

end

/-- Canonical textbook surface for inverse addition. -/
scoped[Rockafellar] notation:65 C₁ " #[" R "] " C₂ =>
  Set.inverseAddition R C₁ C₂

open scoped Rockafellar

section

variable {R : Type*}
variable [Zero R] [One R] [Add R] [LT R]
variable {E : Type u}
variable [SMul R E]

/-- Primitive membership form for inverse addition: strict positive normalized coefficients. -/
@[simp] theorem Set.mem_inverseAddition_primitive_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ (C₁ #[R] C₂) ↔
      ∃ t₁ t₂ : R, 0 < t₁ ∧ 0 < t₂ ∧ t₁ + t₂ = (1 : R) ∧ x ∈ t₁ • C₁ ∩ t₂ • C₂ := by
  rfl

end

section

variable {R : Type*}
variable [AddGroup R] [Preorder R] [AddRightStrictMono R] [One R]
variable {E : Type u}
variable [SMul R E]

/-- Membership bridge to the one-parameter textbook surface `(1 - λ) • C₁ ∩ λ • C₂`
for `0 < λ < 1`, in primitive inequality form. -/
theorem Set.mem_inverseAddition_iff_exists_pos_lt (C₁ C₂ : Set E) (x : E) :
    x ∈ (C₁ #[R] C₂) ↔
      ∃ t : R, 0 < t ∧ t < (1 : R) ∧ x ∈ (1 - t) • C₁ ∩ t • C₂ := by
  rw [Set.mem_inverseAddition_primitive_iff]
  constructor
  · rintro ⟨t₁, t₂, ht₁, ht₂, hsum, hx⟩
    have ht₂_lt_one : t₂ < (1 : R) := by
      have : t₂ < t₁ + t₂ := lt_add_of_pos_left t₂ ht₁
      simpa [hsum] using this
    have ht₁_eq : t₁ = 1 - t₂ :=
      (eq_sub_iff_add_eq).2 hsum
    refine ⟨t₂, ht₂, ht₂_lt_one, ?_⟩
    exact ⟨by simpa [ht₁_eq] using hx.1, hx.2⟩
  · rintro ⟨t, ht0, ht1, hx⟩
    refine ⟨1 - t, t, sub_pos.2 ht1, ht0, sub_add_cancel (1 : R) t, hx⟩

/-- Membership bridge to the one-parameter textbook surface `(1 - λ) • C₁ ∩ λ • C₂`
for `0 < λ < 1`, packaged through interval notation. -/
@[simp] theorem Set.mem_inverseAddition_iff (C₁ C₂ : Set E) (x : E) :
    x ∈ (C₁ #[R] C₂) ↔
      ∃ t, t ∈ Set.Ioo (0 : R) (1 : R) ∧ x ∈ (1 - t) • C₁ ∩ t • C₂ := by
  simpa [Set.Ioo, and_assoc] using
    (Set.mem_inverseAddition_iff_exists_pos_lt C₁ C₂ x)

end
