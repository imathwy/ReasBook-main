import Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_definition_4_7_extra_1

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

-- This file reuses the canonical Section 4.7 owner `Submodular` and adds the
-- submodular polyhedron and greedy constructions built from it.

section Remark_4_7_extra_2

section Polyhedron

variable {α : Type*}

/-- The submodular polyhedron attached to a real-valued set function `f`. -/
def submodularPolyhedron (f : Finset α → ℝ) : Set (α → ℝ) :=
  {x | ∀ S : Finset α, (∑ j ∈ S, x j) ≤ f S}

/-- Membership in `submodularPolyhedron` is equivalent to satisfying all subset inequalities. -/
@[simp] theorem mem_submodularPolyhedron_iff {f : Finset α → ℝ} {x : α → ℝ} :
    x ∈ submodularPolyhedron f ↔
      ∀ S : Finset α, (∑ j ∈ S, x j) ≤ f S :=
  Iff.rfl

end Polyhedron

section Greedy

variable {n : ℕ}

/-- The `j`-th greedy prefix set on `Fin n`, namely the indices whose zero-based value is `< j`.
This is the `Fin`-indexed translation of the textbook chain `S₀ = ∅`, `Sⱼ = {1, ..., j}`. -/
def submodularGreedyPrefix (n : ℕ) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ i.1 < j

/-- Membership in `submodularGreedyPrefix n j` means exactly that the index lies among the first
`j` coordinates. -/
@[simp] theorem mem_submodularGreedyPrefix_iff (n : ℕ) (j : ℕ) (i : Fin n) :
    i ∈ submodularGreedyPrefix n j ↔ i.1 < j := by
  simp [submodularGreedyPrefix]

/-- The primitive greedy increments attached to an integer-valued submodular set function. -/
def submodularGreedySolutionInt (f : Finset (Fin n) → ℤ) : Fin n → ℤ :=
  fun j ↦
    f (submodularGreedyPrefix n (j.1 + 1)) - f (submodularGreedyPrefix n j.1)

/-- The real-valued greedy vector is the canonical coercion of the integer greedy increments. -/
abbrev submodularGreedySolution (f : Finset (Fin n) → ℤ) : Fin n → ℝ :=
  Int.cast ∘ submodularGreedySolutionInt f

/-- Remark 4.7-extra-2. If the objective coefficients are ordered so that they are antitone and
nonnegative, then the greedy vector obtained from successive prefix differences is an optimal
solution of the submodular maximization problem `(4.24)`. -/
theorem submodularGreedySolution_optimal
    (f : Finset (Fin n) → ℤ)
    (c : Fin n → ℤ)
    (h_submodular : Submodular f)
    (h_empty : f ∅ = 0)
    (h_antitone : Antitone c)
    (h_nonneg : ∀ j, 0 ≤ c j) :
    submodularGreedySolution f ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) ∧
      ∀ x : Fin n → ℝ,
        x ∈ submodularPolyhedron (fun S ↦ (f S : ℝ)) →
          (∑ j, (c j : ℝ) * x j) ≤
            ∑ j, (c j : ℝ) * submodularGreedySolution f j := sorry

end Greedy

end Remark_4_7_extra_2
