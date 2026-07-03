import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace CategoryTheory

/-
Domain-style sampling for Lemma 19.12.1:
- primary domain: generators/strong generators in Grothendieck abelian categories, together with
  subobject-cardinality bounds;
- sampled owner declarations:
  `IsSeparator`,
  `isSeparator_iff_exists_not_factors_subobject`,
  `exists_epi_from_coproduct_of_generator_of_subobject_cardinal_le`,
  `Cardinal.mk (Subobject X)`;
- best owner abstraction: the generator input is canonically `IsSeparator U`, while the
  size parameter is the canonical owner `Cardinal.mk (Subobject N)` with its `w`-small model
  `Shrink.{w} (Subobject N)` rather than an auxiliary existential index type;
- primitive data: a separator `U`, an epimorphism `π : M ⟶ N`, and the proper subobjects of `N`;
- derived API: a subobject `M' : Subobject M` with `Epi (M'.arrow ≫ π)` and the induced
  subobject-cardinality bound coming from the canonical coproduct indexed by
  `Shrink.{w} (Subobject N)`.

Source/core/bridge triage:
- `source-facing`: the bounded subobject `M' ⊆ M` that still surjects onto `N`;
- `core/canonical`: `IsSeparator`, `Cardinal.mk (Subobject _)`, and the canonical small model
  `Shrink.{w} (Subobject _)`;
- `bridge/view`: this theorem, which converts the generator-side owner abstractions into the
  Stacks-project bounded-subobject statement. -/

/-- Lemma 19.12.1: if `π : M ⟶ N` is an epimorphism in a Grothendieck abelian category with
source-facing generator `U`, formalized by `IsSeparator U`, then some subobject `M' ⊆ M` still
surjects onto `N`, and `Subobject M'` is bounded in cardinality by the subobject lattice of the
coproduct of copies of `U` indexed by the canonical `w`-small model `Shrink.{w} (Subobject N)` of
the subobject lattice of `N`. -/
-- Proof sketch: use the separator/strong-generator criterion to choose, for each proper
-- subobject `N' ⊊ N`, a map `U ⟶ M` whose composite with `π` does not factor through `N'`.
-- Assemble these maps into a morphism from the canonical coproduct indexed by
-- `Shrink.{w} (Subobject N)`, let `M'` be its image in `M`, and then use the Chapter 19
-- subobject-cardinality lemmas for subobjects and quotients to bound
-- `Cardinal.mk (Subobject (M' : C))` by the corresponding coproduct bound.
theorem exists_subobject_surjecting_onto_of_epi_le_generator_coproduct_size
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {U M N : C} (hU : IsSeparator U) (π : M ⟶ N) [Epi π] :
    ∃ M' : Subobject M,
      Epi (M'.arrow ≫ π) ∧
        Cardinal.mk (Subobject (M' : C)) ≤
          Cardinal.mk (Subobject (∐ fun _ : Shrink.{w} (Subobject N) ↦ U)) := sorry

end CategoryTheory
