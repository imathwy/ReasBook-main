import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_90_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R]

/- Domain triage: this proposition relates coherence of a commutative ring to flatness of
arbitrary products.
- `source-facing`: the TFAE comparing the Stacks ideal-theoretic coherence condition with flatness
  of products.
- `core/canonical`: the chapter owner predicate `IsCoherentRing R`.
- `bridge/view`: the textbook clause "every finitely generated ideal is finitely presented" is a
  source-facing reformulation of `IsCoherentRing R`, not a separate owner abstraction.
Primitive data are only the ring and the chosen family of modules; finite presentation of ideals is
derived API of the owner predicate. -/

-- Proof sketch: `(1) → (2)` uses the ideal-theoretic flatness criterion from Lemma `10.39.5`.
-- For a finitely generated ideal `I`, coherence gives finite presentation, so Proposition
-- `10.89.3` identifies `I ⊗[R] ∏ Mₐ` with `∏ (I ⊗[R] Mₐ)`, and injectivity follows
-- componentwise from the flatness of each factor. `(2) → (3)` is the specialization to the
-- constant family with each factor equal to `R`. For `(3) → (1)`, Proposition `10.89.2`
-- identifies the image of `I ⊗[R] R^A → R^A` with `I^A`, and Proposition `10.89.3` then forces
-- each finitely generated ideal `I` to be finitely presented, i.e. the canonical owner predicate
-- `IsCoherentRing R` holds.
/-- Proposition 10.90.6: the following are equivalent for a commutative ring `R`: `R` is coherent
(expressed by the owner predicate `IsCoherentRing R`), arbitrary products of flat `R`-modules are
flat, and for every set `A` the product module `A → R` is flat. -/
theorem coherent_tfae_flat_products :
    List.TFAE
      [ IsCoherentRing R,
        ∀ (A : Type v) (M : A → Type w) [∀ a, AddCommGroup (M a)] [∀ a, Module R (M a)],
          (∀ a, Module.Flat R (M a)) → Module.Flat R (∀ a, M a),
        ∀ A : Type v, Module.Flat R (A → R) ] := sorry

end
