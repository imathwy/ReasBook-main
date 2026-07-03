import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_9_4_1 (from Chap09) -/
universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/- Domain-style sampling for Lemma 9.4.1:
- primary domain: linear algebra over a field, specifically the freeness of vector spaces;
- sampled owner declarations:
  `Module.Free`,
  `Module.Free.of_basis`,
  `Module.Free.chooseBasis`,
  `Module.Free.of_divisionRing`;
- best owner abstraction: `Module.Free k V`;
- primitive data: none in this file beyond the ambient field/module structure, since freeness is
  already owned canonically by the `Module.Free` class;
- derived API: any chosen basis or coordinate description, for example via
  `Module.Free.chooseBasis`, is downstream derived data and should not be made primitive here.

Source/core/bridge triage:
- `source-facing`: the statement that every `k`-module is free when `k` is a field;
- `core/canonical`: the owner predicate `Module.Free k V`;
- `bridge/view`: the field-specialized recall of the existing division-ring instance
  `Module.Free.of_divisionRing`.

This item is therefore a `bridge/view` recall. The faithful refinement is to reuse the existing
owner-level theorem directly, rather than introduce any local wrapper or a basis-valued
reformulation as a new public API. -/

/- Lemma 9.4.1: if `k` is a field, then every `k`-module is a free `k`-module. This is the
canonical mathlib theorem `Module.Free.of_divisionRing`, specialized to the field case. -/
recall Module.Free.of_divisionRing

/-! ### Lemma_9_4_2 (from Chap09) -/
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
theorem exact_sequence_of_modules_over_field_splits
    {f : V →ₗ[k] W} {g : W →ₗ[k] X}
    (hfg : Function.Exact f g) (hf : Function.Injective f) (hg : Function.Surjective g) :
    ∃ e : W ≃ₗ[k] V × X, f = e.symm ∘ₗ inl k V X ∧ g = snd k V X ∘ₗ e := by
  exact ((hfg.split_tfae hf hg).out 0 2 rfl rfl).mp <|
    Module.projective_lifting_property g (LinearMap.id : X →ₗ[k] X) hg

end
