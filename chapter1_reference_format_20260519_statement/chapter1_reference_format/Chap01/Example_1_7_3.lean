import chapter1_reference_format.Chap01.Example_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v}

/- Example 1.7.3 (1): a self-map `f : X → X` is the identity map exactly when it fixes every
point of `X`. This is already the earlier chapter theorem
`eq_id_iff_forall_apply_eq_self`. -/
recall eq_id_iff_forall_apply_eq_self {f : X → X} :
    f = id ↔ ∀ x : X, f x = x

/- Example 1.7.3 (2): if the image `f(X)` is the singleton `{y}`, then `f` is the constant map
with value `y`. This is the source-facing function-level consequence of the canonical singleton-
range API `Function.apply_eq_of_range_eq_singleton`. -/
theorem eq_const_of_range_eq_singleton {f : X → Y} {y : Y}
    (hy : Set.range f = ({y} : Set Y)) : f = Function.const X y := by
  funext x
  exact Function.apply_eq_of_range_eq_singleton hy x

/- Example 1.7.3 (3): a bijective self-map of `X` is represented by a permutation
`σ : Equiv.Perm X`. This is already the earlier chapter theorem
`exists_perm_of_bijective`. -/
recall exists_perm_of_bijective {f : X → X} :
    Function.Bijective f ↔ ∃ σ : Equiv.Perm X, (σ : X → X) = f
