import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_12
import Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13

noncomputable section

section Lemma715

/-- The candidate values in the recursive update `(7.19)` that produces the next source function
from the previous stage by optimizing over the one-step flow set. -/
def flow_cover_recursive_lifting_step_values
    (b a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i z : ℝ) : Set ℝ :=
  {v | ∃ p : (Fin 1 → ℝ) × (Fin 1 → ℝ),
      p ∈ one_step_flow_set a_i ∧
        z + p.2 0 ∈ Set.Icc (0 : ℝ) b ∧
          v = f_i (z + p.2 0) - (α_i * p.2 0 + β_i * p.1 0)}

/-- Membership in `flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z` is exactly the
optimization relation appearing in `(7.19)`. -/
@[simp] theorem mem_flow_cover_recursive_lifting_step_values_iff
    {b a_i : ℝ} {f_i : ℝ → ℝ} {α_i β_i z v : ℝ} :
    v ∈ flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z ↔
      ∃ p : (Fin 1 → ℝ) × (Fin 1 → ℝ),
        p ∈ one_step_flow_set a_i ∧
          z + p.2 0 ∈ Set.Icc (0 : ℝ) b ∧
            v = f_i (z + p.2 0) - (α_i * p.2 0 + β_i * p.1 0) :=
  Iff.rfl

/-- The recursive update `(7.19)` sending `f_i` to the next function. -/
noncomputable def flow_cover_recursive_lifting_step
    (b a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i : ℝ) (z : ℝ) : ℝ :=
  sInf (flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z)

/-- Expanding `flow_cover_recursive_lifting_step` recovers the infimum formula from `(7.19)`. -/
theorem flow_cover_recursive_lifting_step_eq
    (b a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i z : ℝ) :
    flow_cover_recursive_lifting_step b a_i f_i α_i β_i z =
      sInf (flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z) :=
  rfl

/-- The stage-indexed recursive functions from `(7.19)`, rooted at the canonical flow-cover
lifting function. The stage `0` term is the source function `f`, and stage `k + 1` is obtained by
applying `(7.19)` with the coefficient triple indexed by `k`. -/
noncomputable def flow_cover_recursive_lifting_function
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ) (i : ℕ) : ℝ → ℝ :=
  Nat.rec
    (flow_cover_lifting_function
      b
      (flow_cover_excess coverCapacity b Finset.univ)
      coverCapacity)
    (fun k f_k ↦
      if hk : k < m then
        flow_cover_recursive_lifting_step
          b
          (liftCapacity ⟨k, hk⟩)
          f_k
          (α ⟨k, hk⟩)
          (β ⟨k, hk⟩)
      else
        f_k)
    i

/-- Stage `0` of the recursive family `(7.19)` is the canonical flow-cover lifting function. -/
@[simp] theorem flow_cover_recursive_lifting_function_zero
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ) :
    flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β 0 =
      flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity :=
  rfl

/-- When `k < m`, the recursive family satisfies the one-step update formula `(7.19)` at stage
`k + 1`. -/
theorem flow_cover_recursive_lifting_function_succ
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    {k : ℕ} (hk : k < m) :
    flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β (k + 1) =
      flow_cover_recursive_lifting_step
        b
        (liftCapacity ⟨k, hk⟩)
        (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β k)
        (α ⟨k, hk⟩)
        (β ⟨k, hk⟩) := by
  simp [flow_cover_recursive_lifting_function, hk]

/-- Lemma 7.15. Let `f` be the canonical flow-cover lifting function from Lemmas 7.13 and 7.14,
and let `flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i` be the stage
`i` function defined recursively by `(7.19)`. If each one-step pair `(α_i, β_i)` is valid on the
corresponding one-step flow set, then every recursive stage coincides with `f` on `0 ≤ z ≤ b`. -/
theorem flow_cover_recursive_lifting_eq_lifting_function
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    (hvalid :
      ∀ i : Fin m,
        one_step_lifting_valid
          (liftCapacity i)
          (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i)
          (α i)
          (β i))
    (i : Fin (m + 1)) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i z =
      flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity z := by
  sorry

end Lemma715
