import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v}

open Function

-- Proof sketch: use `funext` to convert the pointwise condition `∀ x, f x = x` into equality with
-- `id`, and read the converse by evaluating the equality at each point.
/-- Example 1.1.3 (1): a transformation `f : X → X` is the identity map exactly when it is the
canonical self-map `id`, equivalently when `f x = x` for every `x : X`. -/
theorem eq_id_iff_forall_apply_eq_self {f : X → X} :
    f = id ↔ ∀ x : X, f x = x := by
  simpa [IsFixedPt, eq_comm] using
    (show (∀ x : X, IsFixedPt f x) ↔ f = id from forall_isFixedPt_iff).symm

-- Proof sketch: use the canonical singleton-range API to identify the unique value of `f`, then
-- apply `funext`; the converse is the standard range computation for a constant function.
/-- Example 1.1.3 (2): a map `f : X → Y` with image `f(X) = {y}` is exactly the constant map
with value `y`. -/
theorem range_eq_singleton_iff_eq_const [Nonempty X] {f : X → Y} {y : Y} :
    Set.range f = ({y} : Set Y) ↔ f = const X y := by
  constructor
  · intro hy
    funext x
    exact apply_eq_of_range_eq_singleton hy x
  · rintro rfl
    exact Set.range_eq_singleton fun _ ↦ rfl

-- Proof sketch: bundle a bijective self-map using `Equiv.ofBijective`, and recover bijectivity
-- from any permutation by applying `Equiv.bijective` to its underlying function.
/-- Example 1.1.3 (3): a bijective self-map of `X` is represented by a permutation
`σ : Equiv.Perm X`. -/
theorem exists_perm_of_bijective {f : X → X} :
    Bijective f ↔ ∃ σ : Equiv.Perm X, (σ : X → X) = f := by
  constructor
  · intro hf
    exact ⟨Equiv.ofBijective f hf, rfl⟩
  · rintro ⟨σ, rfl⟩
    exact σ.bijective
