import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `LocallyQuasiFinite` and
-- `Scheme.Hom.fiber`; local Chapter 29 precedent uses `pullback f g` for the base change.

/-- Lemma 29.20.8: for a locally finite type morphism of schemes `f : X ⟶ S`, the following are
equivalent: `f` is locally quasi-finite; every scheme-theoretic fiber `X_s` has discrete
underlying topological space; and for every morphism `Spec(k) ⟶ S` from the spectrum of a field,
the base change `X_k` has discrete underlying topological space. -/
@[stacks 06RT]
theorem locallyQuasiFinite_tfae_discrete_fibers_and_field_base_changes
    [LocallyOfFiniteType f] :
    List.TFAE
      [ LocallyQuasiFinite f
      , ∀ s : S, DiscreteTopology (f.fiber s)
      , ∀ (k : Type u) [Field k] (g : Spec (CommRingCat.of k) ⟶ S),
          DiscreteTopology (pullback f g : Scheme)
      ] := sorry

end AlgebraicGeometry
