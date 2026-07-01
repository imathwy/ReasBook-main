import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U X : C}

/- Domain-style sampling for Lemma 19.11.1:
- primary domain: the ordered type `Subobject X` in an abelian category, with size controlled by a
  separator `U` through the hom-set `U ⟶ X`;
- core/canonical owners: `Subobject X`, `IsSeparator U`, and the ambient chain-condition owners
  `IsNoetherianObject X` / `IsArtinianObject X`;
- primitive data: the objects `U` and `X`, the generator hypothesis `IsSeparator U`, and the
  canonical cardinal comparison involving `Cardinal.mk (U ⟶ X)`;
- derived API: the source-facing prohibitions on strict chains, the stabilization of monotone or
  antitone ordinal-indexed chains, and the cardinal bound on `Subobject X`.

Source/core/bridge triage:
- `source-facing`: the five lemmas below are the Stacks-project cardinal consequences for
  subobject chains;
- `core/canonical`: the underlying owner abstractions are `Subobject X` and the usual
  noetherian/artinian chain conditions on that order;
- no new `bridge/view` owner is introduced here, since the source statements add the explicit
  hom-cardinality bounds rather than merely recalling the owner notions.
-/

/-- Lemma 19.11.1 (1): if `U` is a generator of the abelian category and
`#(U ⟶ X) < κ'`, then there is no strictly increasing chain of subobjects of `X`
indexed by `κ'`. -/
-- Proof sketch: for each strict step in the chain, use that `U` is a generator to choose a
-- morphism `U ⟶ X` factoring through the larger subobject but not the smaller one; these
-- morphisms are pairwise distinct, contradicting the cardinality bound `#(U ⟶ X) < κ'`.
lemma no_strictly_increasing_subobject_chain_of_gt_hom_card
    (hU : IsSeparator U) (κ' : Cardinal.{v}) (hκ' : Cardinal.mk (U ⟶ X) < κ') :
    ¬ ∃ A : κ'.ord.ToType → Subobject X, StrictMono A := sorry

/-- Lemma 19.11.1 (2): if `U` is a generator of the abelian category and
`#(U ⟶ X) < κ'`, then there is no strictly decreasing chain of subobjects of `X`
indexed by `κ'`. -/
-- Proof sketch: pass to the opposite abelian category, where subobjects of `X` become
-- subobjects of `op X` with the order reversed, and apply the increasing-chain statement there.
lemma no_strictly_decreasing_subobject_chain_of_gt_hom_card
    (hU : IsSeparator U) (κ' : Cardinal.{v}) (hκ' : Cardinal.mk (U ⟶ X) < κ') :
    ¬ ∃ A : κ'.ord.ToType → Subobject X, StrictAnti A := sorry

/-- Lemma 19.11.1 (3): if `U` is a generator of the abelian category,
and `α` has cofinality greater than `#(U ⟶ X)`, then every increasing
`α`-indexed sequence of subobjects of `X` is eventually constant. -/
-- Proof sketch: if the sequence were not eventually constant, one extracts a cofinal strictly
-- increasing subsequence indexed by a set of cardinality at most `α.cof`, contradicting the
-- preceding no-chain result when `#(U ⟶ X) < α.cof`.
lemma monotone_subobject_sequence_eventually_constant_of_cof_gt_hom_card
    (hU : IsSeparator U) (α : Ordinal.{v}) (hα : Cardinal.mk (U ⟶ X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Monotone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := sorry

/-- Lemma 19.11.1 (4): if `U` is a generator of the abelian category,
and `α` has cofinality greater than `#(U ⟶ X)`, then every decreasing
`α`-indexed sequence of subobjects of `X` is eventually constant. -/
-- Proof sketch: apply the increasing-sequence statement in the opposite abelian category, where
-- decreasing chains of subobjects become increasing chains.
lemma antitone_subobject_sequence_eventually_constant_of_cof_gt_hom_card
    (hU : IsSeparator U) (α : Ordinal.{v}) (hα : Cardinal.mk (U ⟶ X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Antitone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := sorry

/-- Lemma 19.11.1 (5): if `U` is a generator of the abelian category, then the set of
subobjects of `X` has cardinality at most `2 ^ #(U ⟶ X)`. -/
-- Proof sketch: send a subobject `Y ≤ X` to the set of morphisms `U ⟶ X` factoring through `Y`;
-- the generator hypothesis makes this assignment injective, so `Subobject X` embeds into the
-- power set of `Hom(U, X)`.
lemma mk_subobject_le_two_pow_lift_hom_card
    (hU : IsSeparator U) :
    Cardinal.mk (Subobject X) ≤ 2 ^ Cardinal.lift (Cardinal.mk (U ⟶ X)) := sorry
