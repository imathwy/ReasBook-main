import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.ResidueField

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Source/core/bridge triage:
-- - `source-facing`: the singleton-image factorization statement from Stacks, Lemma 29.58.1;
-- - `core/canonical`: the canonical point morphism `Scheme.fromSpecResidueField`;
-- - `bridge/view`: the existence of a factorization through that canonical morphism.

/-- Lemma 29.58.1: if `f : Y ⟶ X` is a morphism of schemes, `Y` is reduced, and the set-theoretic
image of `f` is contained in `{x}`, then `f` factors through the canonical morphism
`Spec (κ(x)) ⟶ X`. -/
@[stacks 0H1M]
theorem exists_factorization_fromSpecResidueField_of_range_subset_singleton
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y]
    (himage : Set.range f ⊆ {x}) :
    ∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f := sorry

/-- The image of `f` is contained in `{x}` if and only if `f` sends every point of `Y` to `x`. -/
theorem range_subset_singleton_iff_forall_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) :
    Set.range f ⊆ {x} ↔ ∀ y : Y, f y = x := by
  constructor
  · intro himage y
    exact Set.mem_singleton_iff.mp (himage ⟨y, rfl⟩)
  · intro h y hy
    rcases hy with ⟨z, rfl⟩
    exact Set.mem_singleton_iff.mpr (h z)

/-- Pointwise companion to Lemma 29.58.1: if a morphism from a reduced scheme sends every point to
`x`, then it factors through the canonical residue-field point `Spec (κ(x)) ⟶ X`. -/
theorem exists_factorization_fromSpecResidueField_of_forall_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y]
    (hpoint : ∀ y : Y, f y = x) :
    ∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f := by
  apply exists_factorization_fromSpecResidueField_of_range_subset_singleton
  exact (range_subset_singleton_iff_forall_eq f x).2 hpoint

/-- For a reduced source, factoring through `Spec (κ(x)) ⟶ X` is equivalent to having
set-theoretic image contained in `{x}`. -/
@[stacks 0H1M]
theorem exists_factorization_fromSpecResidueField_iff_range_subset_singleton
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y] :
    (∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f) ↔
      Set.range f ⊆ {x} := sorry

/-- Pointwise companion to the factorization criterion: for a reduced source, factoring through
`Spec (κ(x)) ⟶ X` is equivalent to sending every point of `Y` to `x`. -/
theorem exists_factorization_fromSpecResidueField_iff_forall_eq
    {X Y : Scheme.{u}} (f : Y ⟶ X) (x : X) [IsReduced Y] :
    (∃ g : Y ⟶ Spec (X.residueField x), g ≫ X.fromSpecResidueField x = f) ↔
      ∀ y : Y, f y = x := by
  rw [exists_factorization_fromSpecResidueField_iff_range_subset_singleton]
  exact range_subset_singleton_iff_forall_eq f x

end AlgebraicGeometry
