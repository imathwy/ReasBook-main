import Mathlib
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap13.Definition_13_34_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite OrderHom
open scoped BigOperators

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 15.87.4:
- primary domain: sequential inverse systems of abelian groups, their associated sequential
  pro-objects, and the Milnor presentations of `\varprojlim` and `R^1 \!\varprojlim`;
- sampled owner declarations:
  `SequentialProObjectMorphismRep.toProObjectHom`,
  `exists_representative`,
  `represents_eq_iff_equivalent`,
  `derivedLimitDifferenceMap`,
  `limit`,
  `cokernel.map`;
- best owner abstraction: a morphism of the associated sequential pro-objects, written directly as
  the canonical Chapter 4 pro-object morphism type
  `colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor A ⋙ uliftFunctor.{0}`;
  a sequential representative is only bridge data used to construct the Milnor comparison maps;
- primitive data: the towers `A`, `B`, and the pro-morphism `η`;
- derived API: the induced maps on `limit A` and
  `SequentialInverseSystem.firstDerivedLimit A`, with representative-level `CommSq` and cokernel
  maps used only to descend those constructions from `η`.

Source/core/bridge triage:
- `source-facing`: the maps induced on `\varprojlim` and on `R^1 \!\varprojlim` by a morphism of
  pro-systems;
- `core/canonical`: `SequentialProObjectMorphismRep.toProObjectHom`, `limit`,
  `derivedLimitDifferenceMap`, and `cokernel.map`;
- `bridge/view`: the Milnor `CommSq` and the representative-level maps attached to a chosen
  sequential representative. -/

namespace SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] [HasLimitsOfShape ℕᵒᵖ C]
variable {A B : SequentialInverseSystem C}

/-- The representative-level map on inverse limits attached to a sequential representative of a
pro-system morphism. This is bridge data for the owner-level map `inducedLimitMap`. -/
def limitMap (r : SequentialProObjectMorphismRep A B) :
    limit A ⟶ limit B :=
  limit.pre A (toFunctor r.reindex).op ≫ limMap r.hom

/-- The induced map on inverse limits of a sequential representative is computed componentwise by
the representative-level maps. -/
theorem limitMap_π (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    r.limitMap ≫ limit.π B (op n) =
      limit.π A (op (r.reindex n)) ≫ r.map n := by
  rw [limitMap, Category.assoc, limMap_π, ← Category.assoc, limit.pre_π]
  simp [toFunctor]

-- Proof sketch: if two representatives define the same pro-object morphism, Example `4.22.6`
-- identifies them after common refinement; the Stacks Project argument shows that the induced map
-- on the canonical inverse-limit object is unchanged by passing to such a refinement.
/-- Representatives defining the same pro-object morphism induce the same map on inverse limits.
-/
private theorem limitMap_eq_of_toProObjectHom_eq
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    r₁.limitMap = r₂.limitMap := sorry

end

section

variable {A B : SequentialInverseSystem AddCommGrpCat.{v}}

/-- The map on ambient products given by the component maps
`A_{m_n} ⟶ B_n` of a sequential representative. -/
private abbrev firstProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦
    Pi.π (inverseSystemFamily A) (r.reindex n) ≫ r.map n

/-- The `n`-th component of the second Milnor product map attached to a sequential representative,
given by summing the transition maps over the interval `[m_n, m_{n + 1})`. -/
private abbrev secondProductComponent (r : SequentialProObjectMorphismRep A B) (n : ℕ) :
    (∏ᶜ inverseSystemFamily A) ⟶ B.obj (op n) :=
  Finset.sum (Finset.range (r.reindex (n + 1) - r.reindex n)) fun k ↦
    Pi.π (inverseSystemFamily A) (r.reindex n + k) ≫
      A.transitionMap (Nat.le_add_right (r.reindex n) k) ≫ r.map n

/-- The second map on ambient products attached to a sequential representative, making the Milnor
square commute. -/
private def secondProductMap (r : SequentialProObjectMorphismRep A B) :
    (∏ᶜ inverseSystemFamily A) ⟶ (∏ᶜ inverseSystemFamily B) :=
  Pi.lift fun n ↦ secondProductComponent r n

-- Proof sketch: compare the `n`-th product projection on both sides. Expanding the definition of
-- `derivedLimitDifferenceMap` and the finite sum in `secondProductComponent`, the terms telescope,
-- and the compatibility relation `r.comm` identifies the remaining boundary terms with the
-- `n`-th component of `firstProductMap r ≫ derivedLimitDifferenceMap B`.
/-- The two product maps attached to a sequential representative form a commutative square with
the Milnor difference maps. -/
private theorem milnorDifferenceCommSq (r : SequentialProObjectMorphismRep A B) :
    CommSq (derivedLimitDifferenceMap A) (firstProductMap r) (secondProductMap r)
      (derivedLimitDifferenceMap B) := sorry

/-- The representative-level map on `R^1 \!\varprojlim`, obtained from the Milnor square attached
to a sequential representative. -/
abbrev firstDerivedLimitMap (r : SequentialProObjectMorphismRep A B) :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  cokernel.map (derivedLimitDifferenceMap A) (derivedLimitDifferenceMap B)
    (firstProductMap r) (secondProductMap r) (milnorDifferenceCommSq r).w

-- Proof sketch: use the same common-refinement argument as for `limitMap`; after passing to
-- cokernels of the Milnor difference maps, the two second product maps define the same morphism.
/-- Representatives defining the same pro-object morphism induce the same map on
`R^1 \!\varprojlim`. -/
private theorem firstDerivedLimitMap_eq_of_toProObjectHom_eq
    {r₁ r₂ : SequentialProObjectMorphismRep A B}
    (h : r₁.toProObjectHom = r₂.toProObjectHom) :
    r₁.firstDerivedLimitMap = r₂.firstDerivedLimitMap := sorry

end

end SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] [HasLimitsOfShape ℕᵒᵖ C]
variable {A B : SequentialInverseSystem C}
variable (η : colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶
  proSystemHomColimitFunctor A ⋙ uliftFunctor.{0})

private noncomputable abbrev chosenRepresentative :
    SequentialProObjectMorphismRep A B :=
  Classical.choose (exists_representative η)

set_option linter.unusedSectionVars false in
private theorem chosenRepresentative_spec :
    (chosenRepresentative η).toProObjectHom = η :=
  Classical.choose_spec (exists_representative η)

/-- The map on inverse limits induced by a morphism between the sequential pro-objects associated
to `A` and `B`. -/
noncomputable def inducedLimitMap :
    limit A ⟶ limit B :=
  (chosenRepresentative η).limitMap

/-- The owner-level map `inducedLimitMap η` is characterized by any sequential representative of
`η`. -/
theorem inducedLimitMap_eq_limitMap
    (r : SequentialProObjectMorphismRep A B) (h : r.toProObjectHom = η) :
    inducedLimitMap η = r.limitMap := by
  exact SequentialProObjectMorphismRep.limitMap_eq_of_toProObjectHom_eq
    ((chosenRepresentative_spec η).trans h.symm)

-- Proof sketch: choose a sequential representative `r` of `η` using Example `4.22.6`. If `η` is
-- an isomorphism in the pro-category, then `inducedLimitMap η` may be computed using `r.limitMap`;
-- applying the same construction to `inv η` gives the inverse map on inverse limits.
/-- An isomorphism between sequential pro-objects induces an isomorphism on inverse limits. -/
theorem inducedLimitMap_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedLimitMap η) := sorry

end

section

variable {A B : SequentialInverseSystem AddCommGrpCat.{v}}
variable (η : colimit (B.op ⋙ uliftCoyoneda.{0}) ⟶
  proSystemHomColimitFunctor A ⋙ uliftFunctor.{0})

/-- The map on `R^1 \!\varprojlim` induced by a morphism between the sequential pro-objects
associated to `A` and `B`. -/
noncomputable def inducedFirstDerivedLimitMap :
    A.firstDerivedLimit ⟶ B.firstDerivedLimit :=
  (chosenRepresentative η).firstDerivedLimitMap

/-- The owner-level map `inducedFirstDerivedLimitMap` agrees with the representative-level bridge
map for any sequential representative of `η`. -/
theorem inducedFirstDerivedLimitMap_eq_firstDerivedLimitMap
    (r : SequentialProObjectMorphismRep A B) (h : r.toProObjectHom = η) :
    inducedFirstDerivedLimitMap η = r.firstDerivedLimitMap := by
  exact SequentialProObjectMorphismRep.firstDerivedLimitMap_eq_of_toProObjectHom_eq
    ((chosenRepresentative_spec η).trans h.symm)

-- Proof sketch: choose a sequential representative `r` of `η` using Example `4.22.6`. If `η` is
-- an isomorphism in the pro-category, then the induced maps on `limit` and on `R^1 \!\varprojlim`
-- are independent of the chosen representative and hence may be computed using any representative
-- of `η`; for that representative, the Stacks Project argument gives inverse maps induced by a
-- representative of `inv η`.
/-- Lemma 15.87.4: a morphism of pro-systems of abelian groups induces maps on
`\varprojlim` and on `R^1 \!\varprojlim`. If the corresponding morphism of sequential
pro-objects is an isomorphism, then both induced maps are isomorphisms. -/
theorem inducedLimitMap_and_inducedFirstDerivedLimitMap_are_isIso_of_isIso
    [IsIso η] :
    IsIso (inducedLimitMap η) ∧
      IsIso (inducedFirstDerivedLimitMap η) := sorry

end

end CategoryTheory
