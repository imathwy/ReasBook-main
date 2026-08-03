import Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped Matrix SplitHullNotation

section Corollary57

variable {m n : ℕ}

/-- The restricted matrix obtained from `A` by keeping only the rows indexed by `B`. -/
abbrev basis_row_matrix
    (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Finset (Fin m)) :
    Matrix {i // i ∈ B} (Fin n) ℝ :=
  A.submatrix Subtype.val id

/-- The restricted right-hand side obtained from `b` by keeping only the entries indexed by
`B`. -/
abbrev basis_row_rhs
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) :
    {i // i ∈ B} → ℝ :=
  b ∘ Subtype.val

/-- The row-restricted polyhedron `P_B`, obtained by keeping only the inequalities indexed by
`B`. -/
def P_B
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m)) : Set (Fin n → ℝ) :=
  {x : Fin n → ℝ | basis_row_matrix A B *ᵥ x ≤ basis_row_rhs b B}

/-- Membership in `P_B` is the restricted-row matrix system cut out by `A` and `b`. -/
theorem mem_P_B_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (x : Fin n → ℝ) :
    x ∈ P_B A b B ↔ basis_row_matrix A B *ᵥ x ≤ basis_row_rhs b B :=
  Iff.rfl

/-- Membership in `P_B` is exactly the family of inequalities indexed by `B`. -/
theorem mem_P_B_rows_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (B : Finset (Fin m))
    (x : Fin n → ℝ) :
    x ∈ P_B A b B ↔ ∀ i : Fin m, i ∈ B → (A *ᵥ x) i ≤ b i :=
by
  constructor
  · intro hx i hi
    rw [mem_P_B_iff] at hx
    simpa [basis_row_matrix, basis_row_rhs] using hx ⟨i, hi⟩
  · intro hx
    rw [mem_P_B_iff]
    intro i
    simpa [basis_row_matrix, basis_row_rhs] using hx i.1 i.2

/-- A row multiplier supported on `B` whose left multiplication with `A` reproduces the split
vector `π`. -/
def IsSupportedSplitRowMultiplier
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m))
    (u : Fin m → ℝ) : Prop :=
  (u ᵥ* A = fun j : Fin n ↦ (π j : ℝ)) ∧
    ∀ i : Fin m, i ∉ B → u i = 0

/-- A supported split row multiplier reproduces `π` and vanishes off `B`. -/
theorem isSupportedSplitRowMultiplier_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m))
    (u : Fin m → ℝ) :
    IsSupportedSplitRowMultiplier A π B u ↔
      (u ᵥ* A = fun j : Fin n ↦ (π j : ℝ)) ∧
        ∀ i : Fin m, i ∉ B → u i = 0 :=
  Iff.rfl

/-- The family of row sets `B` for which the split vector `π` admits a unique supported row
multiplier. The source-facing notation is `𝓑[A, π]`. -/
def splitBasisFamily
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ) : Set (Finset (Fin m)) :=
  {B : Finset (Fin m) | ∃! u : Fin m → ℝ, IsSupportedSplitRowMultiplier A π B u}

namespace SplitBasisNotation

scoped notation:max "𝓑[" A ", " π "]" => splitBasisFamily A π

end SplitBasisNotation

open scoped SplitBasisNotation

/-- Membership in `𝓑` means that `π` admits a unique supported row multiplier for the row set
`B`. -/
theorem mem_𝓑_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (π : Fin n → ℤ)
    (B : Finset (Fin m)) :
    B ∈ 𝓑[A, π] ↔ ∃! u : Fin m → ℝ, IsSupportedSplitRowMultiplier A π B u :=
  Iff.rfl

/-- Corollary 5.7. With the same split data as in Theorem 5.5, the split polyhedron
`P^(π, π₀)` is the intersection of the row-restricted split polyhedra `P_B^(π, π₀)` over all
`B ∈ 𝓑`. -/
theorem split_polyhedron_eq_iInter_P_B
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {I : Finset (Fin n)}
    (s : Split I) :
    split_polyhedron A b s =
      ⋂ B ∈ 𝓑[A, s], (P_B A b B)^(s, s.π0) := sorry

end Corollary57
