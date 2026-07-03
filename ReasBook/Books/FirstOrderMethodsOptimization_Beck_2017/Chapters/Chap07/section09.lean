import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_9 (from Chap07) -/
namespace Function

noncomputable section

section

variable {n : ℕ}

/- Definition 7.9 is `source-facing`: the textbook notion is a proper function on `ℝ^n` that is
invariant under the signed-permutation symmetries collected in `Λ^G_n`. Since the present item
also gives the canonical normal-form characterization `f x = f (|x|↓)`, the clean owner-level
API keeps that canonical representative visible as a concrete rearrangement operator and models the
property itself as a properness class on functions. -/

/-- The decreasing rearrangement of the coordinates of `x`, obtained by sorting the coordinate
list in weakly decreasing order and reading it back as a vector in `ℝ^n`. -/
def descendingRearrangement (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ (((List.ofFn x).mergeSort (· ≥ ·)).getD i 0)

scoped postfix:max "↓" => Function.descendingRearrangement

open scoped Function

-- Proof sketch: unfold `descendingRearrangement`; evaluation at coordinate `i` is definitionally
-- the `i`-th entry of the decreasingly sorted coordinate list.
/-- Evaluating `descendingRearrangement x` returns the corresponding entry of the decreasingly
sorted coordinate list of `x`. -/
theorem descendingRearrangement_apply (x : Fin n → ℝ) (i : Fin n) :
    descendingRearrangement x i = (((List.ofFn x).mergeSort (· ≥ ·)).getD i 0) := by
  -- Unfolding the rearrangement shows that coordinate evaluation is definitional.
  rfl

/-- Definition 7.9: a proper extended-real-valued function on `ℝ^n` is absolutely permutation
symmetric when it depends only on the decreasing rearrangement `|x|↓` of the absolute coordinate
values, equivalently on the signed-permutation orbit of `x`. -/
class IsAbsolutelyPermutationSymmetric (f : (Fin n → ℝ) → EReal) : Prop
    where
  ne_bot : ∀ x, f x ≠ ⊥
  effective_domain_nonempty : {x | f x < ⊤}.Nonempty
  map_eq_abs_descendingRearrangement (x : Fin n → ℝ) : f x = f (|x|↓)

-- Proof sketch: unfold `Function.IsAbsolutelyPermutationSymmetric`; the only extra datum beyond
-- properness is exactly the normal-form identity `f x = f (|x|↓)` for every `x`.
/-- An extended-real-valued function on `ℝ^n` is absolutely permutation symmetric exactly when it
never takes the value `-∞`, has nonempty effective domain, and is unchanged by replacing `x` with
the decreasing rearrangement of its absolute coordinate values. -/
theorem isAbsolutelyPermutationSymmetric_iff_forall_eq_abs_descendingRearrangement
    (f : (Fin n → ℝ) → EReal) :
    IsAbsolutelyPermutationSymmetric f ↔
      (∀ x, f x ≠ ⊥) ∧ {x | f x < ⊤}.Nonempty ∧
        ∀ x : Fin n → ℝ, f x = f (|x|↓) := by
  constructor
  · intro hf
    -- Read the three required properties directly from the class fields.
    exact ⟨hf.ne_bot, hf.effective_domain_nonempty, hf.map_eq_abs_descendingRearrangement⟩
  · rintro ⟨h_ne_bot, h_nonempty, h_map⟩
    -- Repackage the properness data and the rearrangement invariance into the class.
    exact ⟨h_ne_bot, h_nonempty, h_map⟩

-- Proof sketch: the constant zero function is proper, and the defining identity
-- `f x = f (|x|↓)` is immediate because both sides evaluate to `0`.
/-- The constant zero extended-real-valued function on `ℝ^n` is absolutely permutation
symmetric. -/
instance : IsAbsolutelyPermutationSymmetric (fun _ : Fin n → ℝ ↦ (0 : EReal)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    -- The constant zero function never takes the value `-∞`.
    simp
  · -- The origin lies in the effective domain because `0 < ⊤` in `EReal`.
    refine ⟨0, ?_⟩
    simp
  · intro x
    -- Rearranging the input does not change a constant function.
    simp

end

end

end Function

/-! ### Theorem_7_9 (from Chap07) -/
noncomputable section

section

variable {n : ℕ}

/- Theorem 7.9 is `source-facing` in the Chapter 7 symmetry API. The relevant owner declarations
are Chapter 7's `IsSymmetricFunction` for symmetry under a family of orthogonal matrices and
Chapter 4's `conjugate_function` for Fenchel conjugates. The owner abstraction stays on the
textbook coordinate model `ℝ^n`, with orthogonal matrices acting by `mulVec`. -/

/-- Helper for Theorem 7.9: moving an orthogonal matrix from the second dot-product input to the
first input amounts to applying the matrix itself. -/
lemma dotProduct_transpose_mulVec_eq_dotProduct_smul
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (y z : Fin n → ℝ) :
    dotProduct y ((A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z) =
      dotProduct (A • y) z := by
  -- Rewrite the left pairing by moving the transpose to the first vector.
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rfl

/-- Helper for Theorem 7.9: an orthogonal matrix followed by its transpose acts as the identity on
`ℝ^n`. -/
lemma orthogonal_mulVec_transpose_mulVec
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (z : Fin n → ℝ) :
    (A : Matrix (Fin n) (Fin n) ℝ).mulVec
        ((A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z) = z := by
  -- Collapse the composition to the identity matrix using orthogonality.
  rw [Matrix.mulVec_mulVec]
  have hA :
      (A : Matrix (Fin n) (Fin n) ℝ) *
        (A : Matrix (Fin n) (Fin n) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Theorem 7.9: the transpose of an orthogonal matrix is its inverse action on
`ℝ^n`. -/
lemma orthogonal_transpose_mulVec_mulVec
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (x : Fin n → ℝ) :
    ((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec
        ((A : Matrix (Fin n) (Fin n) ℝ).mulVec x) = x := by
  -- Collapse the transpose-after-action composition to the identity matrix.
  rw [Matrix.mulVec_mulVec]
  have hA :
      (A : Matrix (Fin n) (Fin n) ℝ).transpose *
        (A : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 A.2
  rw [hA, Matrix.one_mulVec]

/-- Helper for Theorem 7.9: orthogonal precomposition preserves the range of the conjugate
integrand after the matching change of variables. -/
lemma conjugate_integrand_range_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (f : (Fin n → ℝ) → EReal)
    (y : Fin n → ℝ) :
    Set.range
        (fun x : Fin n → ℝ ↦
          (((dotProductEquiv ℝ (Fin n) y) x : ℝ) : EReal) - f (A • x)) =
      Set.range
        (fun z : Fin n → ℝ ↦
          (((dotProductEquiv ℝ (Fin n) (A • y)) z : ℝ) : EReal) - f z) := by
  ext u
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨A • x, ?_⟩
    simp only
    have hAx : A • x = (A : Matrix (Fin n) (Fin n) ℝ).mulVec x := rfl
    -- Route correction: use the transpose as the explicit inverse action for the change of
    -- variables, rather than searching for a subtype inverse on `Matrix.orthogonalGroup`.
    have hx :
        ((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec (A • x) = x := by
      rw [hAx]
      exact orthogonal_transpose_mulVec_mulVec A x
    have hdot :
        (((dotProductEquiv ℝ (Fin n) y)
            (((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec (A • x)) : ℝ) :
            EReal) =
          (((dotProductEquiv ℝ (Fin n) (A • y)) (A • x) : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y (A • x))
    -- Rewrite the transformed pairing back to the original point `x`.
    rw [← hdot, hx]
  · rintro ⟨z, rfl⟩
    refine ⟨((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec z, ?_⟩
    simp only
    have hz : A • (A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z = z := by
      change (A : Matrix (Fin n) (Fin n) ℝ).mulVec
          (((A : Matrix (Fin n) (Fin n) ℝ).transpose).mulVec z) = z
      exact orthogonal_mulVec_transpose_mulVec A z
    have hdot :
        (((dotProductEquiv ℝ (Fin n) y)
            ((A : Matrix (Fin n) (Fin n) ℝ).transpose.mulVec z) : ℝ) : EReal) =
          (((dotProductEquiv ℝ (Fin n) (A • y)) z : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal))
        (dotProduct_transpose_mulVec_eq_dotProduct_smul A y z)
    -- The transpose-preimage reproduces the target integrand exactly.
    rw [hdot, hz]

/-- Helper for Theorem 7.9: precomposing by an orthogonal matrix transports the conjugate point by
that same matrix. -/
lemma conjugate_function_precompose_orthogonal_eq
    (A : Matrix.orthogonalGroup (Fin n) ℝ) (f : (Fin n → ℝ) → EReal)
    (y : Fin n → ℝ) :
    conjugate_function (fun x : Fin n → ℝ ↦ f (A • x))
        (dotProductEquiv ℝ (Fin n) y) =
      conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) := by
  -- Unfold the conjugate and replace the defining range by the orthogonal change of variables.
  rw [conjugate_function_apply, conjugate_function_apply,
    conjugate_integrand_range_precompose_orthogonal_eq]

-- Proof sketch: fix `A ∈ 𝒜`. Apply the conjugate change-of-variables formula to the linear map
-- `x ↦ A.mulVec x`. The hypothesis `hf` identifies `f ∘ A` with `f`, and orthogonality shows that
-- the Euclidean dual vector corresponding to `A.mulVec y` is exactly the pullback of the dual
-- vector corresponding to `y`. Rewriting the transformed conjugate with these two facts gives the
-- required invariance.
/-- Theorem 7.9: if `f` is symmetric with respect to `𝒜`, then its Fenchel conjugate, viewed on
`ℝ^n` through `dotProductEquiv`, is invariant under every orthogonal matrix in `𝒜`. -/
theorem conjugate_function_eq_conjugate_function_orthogonal_mulVec
    (𝒜 : Set (Matrix.orthogonalGroup (Fin n) ℝ)) (f : (Fin n → ℝ) → EReal)
    (hf : IsSymmetricFunction 𝒜 f) :
    ∀ A : Matrix.orthogonalGroup (Fin n) ℝ, A ∈ 𝒜 →
      ∀ y : Fin n → ℝ,
        conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) =
          conjugate_function f (dotProductEquiv ℝ (Fin n) y) := by
  intro A hA y
  have hpre : (fun x : Fin n → ℝ ↦ f (A • x)) = f := by
    -- Symmetry identifies the orthogonal precomposition of `f` with `f` itself.
    ext x
    exact hf.map_smul A hA x
  calc
    conjugate_function f (dotProductEquiv ℝ (Fin n) (A • y)) =
        conjugate_function (fun x : Fin n → ℝ ↦ f (A • x))
          (dotProductEquiv ℝ (Fin n) y) := by
          symm
          exact conjugate_function_precompose_orthogonal_eq A f y
    _ = conjugate_function f (dotProductEquiv ℝ (Fin n) y) := by
          rw [hpre]

end
