import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_16

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall note: no deferred Lean semantic-search tool such as `lean_leansearch` was
-- available in this runner, so this file uses local repository precedent and spells out the
-- one-dimensional lifting optimization data directly.

section Lemma713

open scoped BigOperators
open OrderedFlowCover

/-- The objective values in the source definition of the lifting function for an ordered flow-cover
`C`. The coordinate `a i` represents the ordered coefficient `a_{j_{i+1}}`. -/
def flow_cover_lifting_objective_values
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z : ℝ) : Set ℝ :=
  {v | ∃ x : Fin t → Bool, ∃ y : Fin t → ℝ,
      (∀ i, 0 ≤ y i) ∧
        (∑ i, y i) ≤ b - z ∧
        (∀ i, y i ≤ a i * (if x i then (1 : ℝ) else 0)) ∧
          v =
            ∑ i, (y i + max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0))}

/-- Membership in `flow_cover_lifting_objective_values b λ a z` is the feasibility-and-objective
condition from the source maximization formula defining the lifting function. -/
@[simp] theorem mem_flow_cover_lifting_objective_values_iff
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z v : ℝ) :
    v ∈ flow_cover_lifting_objective_values b lam a z ↔
      ∃ x : Fin t → Bool, ∃ y : Fin t → ℝ,
        (∀ i, 0 ≤ y i) ∧
          (∑ i, y i) ≤ b - z ∧
          (∀ i, y i ≤ a i * (if x i then (1 : ℝ) else 0)) ∧
            v =
              ∑ i, (y i + max (a i - lam) 0 * (1 - if x i then (1 : ℝ) else 0)) := Iff.rfl

/-- The lifting function for an ordered flow-cover, defined as `b` minus the supremum of the
source optimization problem. -/
noncomputable def flow_cover_lifting_function
    {t : ℕ} (b lam : ℝ) (a : Fin t → ℝ) (z : ℝ) : ℝ :=
  b - sSup (flow_cover_lifting_objective_values b lam a z)

variable {n : ℕ}
variable (a : Fin n → ℝ) (b lam : ℝ) (C : Finset (Fin n))
variable (coverOrder : Fin C.card ↪ Fin n) (r : ℕ)
variable (z : ℝ)

/-- Lemma 7.13 (1). Let `coverOrder` enumerate the elements of the flow cover `C` in
nonincreasing order of their coefficients, let `r` denote the source index
`max {i ∈ C : a_{j_i} > λ}`, and let `μ` be the corresponding sequence `μ_h`. For `z ∈ [0, b]`,
if `μ_h ≤ z < μ_{h+1} - λ` with `h = 0, …, r-1`, then the lifting function for `C` evaluated at
`z` is `h λ`. -/
theorem flow_cover_lifting_function_eq_constant_on_cover_intervals
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder lam r)
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    {h : ℕ} (hh : h < r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h)
        (partialSum C a coverOrder (h + 1) - lam)) :
    flow_cover_lifting_function b lam (a ∘ coverOrder) z =
      (h : ℝ) * lam := sorry

/-- Lemma 7.13 (2). Let `coverOrder` enumerate the elements of the flow cover `C` in
nonincreasing order of their coefficients, let `r` denote the source index
`max {i ∈ C : a_{j_i} > λ}`, and let `μ` be the corresponding sequence `μ_h`. For `z ∈ [0, b]`,
if `μ_h - λ ≤ z < μ_h` with `h = 1, …, r-1`, then the lifting function for `C` evaluated at `z`
is `z - μ_h + h λ`. -/
theorem flow_cover_lifting_function_eq_affine_on_gap_intervals
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder lam r)
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    {h : ℕ} (hh₁ : 1 ≤ h) (hh₂ : h < r)
    (hzpiece :
      z ∈ Set.Ico
        (partialSum C a coverOrder h - lam)
        (partialSum C a coverOrder h)) :
    flow_cover_lifting_function b lam (a ∘ coverOrder) z =
      z - partialSum C a coverOrder h + (h : ℝ) * lam := sorry

/-- Lemma 7.13 (3). Let `coverOrder` enumerate the elements of the flow cover `C` in
nonincreasing order of their coefficients, let `r` denote the source index
`max {i ∈ C : a_{j_i} > λ}`, and let `μ` be the corresponding sequence `μ_h`. For `z ∈ [0, b]`,
if `μ_r - λ ≤ z ≤ b`, then the lifting function for `C` evaluated at `z` is
`z - μ_r + r λ`. -/
theorem flow_cover_lifting_function_eq_affine_on_final_interval
    (hcoverOrder : enumerates C coverOrder)
    (hordered : Antitone fun h : Fin C.card ↦ a (coverOrder h))
    (hr : isCutIndex a C coverOrder lam r)
    (hz : z ∈ Set.Icc (0 : ℝ) b)
    (hzpiece :
      z ∈ Set.Icc (partialSum C a coverOrder r - lam) b) :
    flow_cover_lifting_function b lam (a ∘ coverOrder) z =
      z - partialSum C a coverOrder r + (r : ℝ) * lam := sorry

end Lemma713
