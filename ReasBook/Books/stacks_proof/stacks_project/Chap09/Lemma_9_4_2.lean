import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w z

open LinearMap

section

variable {k : Type u} {V : Type v} {W : Type w} {X : Type z}
variable [DivisionRing k] [AddCommGroup V] [AddCommGroup W] [AddCommGroup X]
variable [Module k V] [Module k W] [Module k X]

-- Domain-style sampling:
-- * primary domain: split short exact sequences of modules over a division ring; the source text is
--   the field-specialized case.
-- * inspected owner declarations: `Function.Exact.split_tfae`,
--   `Module.projective_lifting_property`, `Function.Exact.splitSurjectiveEquiv`, and
--   `Module.Free.of_divisionRing`.
-- * source-facing layer: Lemma 9.4.2 is the source field statement for a short exact sequence
--   `0 → V → W → X → 0` of `k`-vector spaces, refined to the weakest scalar layer used by the
--   canonical owner API.
-- * core/canonical owner: `Function.Exact.split_tfae`, whose third clause is exactly the desired
--   compatible linear equivalence `W ≃ₗ[k] V × X`.
-- * bridge/view: `X` is projective by `Module.Free.of_divisionRing`, so surjectivity of `g`
--   gives a section through `Module.projective_lifting_property`.
-- * primitive data: `Function.Exact f g`, `Function.Injective f`, `Function.Surjective g`.
-- * derived API: a section of `g`, and hence the splitting equivalence `W ≃ₗ[k] V × X`.

/- Core canonical owner for the field-specialized splitting criterion used below. -/
recall Function.Exact.split_tfae

/-- Lemma 9.4.2: the source field statement is a special case of the stronger fact that every short
exact sequence `0 → V → W → X → 0` of modules over a division ring `k` splits, equivalently `W` is
linearly equivalent to `V × X` in a way that identifies `f` with `LinearMap.inl` and `g` with
`LinearMap.snd`. -/
@[stacks 09FP]
theorem exact_sequence_of_modules_over_field_splits
    {f : V →ₗ[k] W} {g : W →ₗ[k] X}
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    ∃ e : W ≃ₗ[k] V × X, f = e.symm ∘ₗ inl k V X ∧ g = snd k V X ∘ₗ e := by
  exact ((hfg.split_tfae hf hg).out 0 2 rfl rfl).mp <|
    Module.projective_lifting_property g (LinearMap.id : X →ₗ[k] X) hg

end
