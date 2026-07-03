import Mathlib
import StacksProject_2024.Chap14.Definition_14_26_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 14.26.6:
- primary domain: simplicial homotopy theory for simplicial objects in an arbitrary category;
- sampled canonical declarations:
  `CategoryTheory.SimplicialObject.Homotopic`,
  `CategoryTheory.SimplicialObject.Homotopy`,
  `Homotopy.refl`,
  `ContinuousMap.HomotopyEquiv`,
  `HomologicalComplex.HomotopyEquiv`,
  `HomologicalComplex.homotopyEquivalences`;
- source/core/bridge triage:
  `source-facing`: `HomotopyEquiv U V`,
  `core/canonical`: the same owner structure, whose primitive data are the forward map, the
    reverse map, and the two simplicial homotopy relations,
  `bridge/view`: the derived morphism property `homotopyEquivalences C` and the high-reuse
    proposition alias `IsHomotopyEquivalence a`.

There is no upstream simplicial-object owner for homotopy equivalences analogous to the chain
complex owner in mathlib, so this file remains the owner. Since Definition 14.26.1 has already
canonicalized simplicial homotopy as the zigzag relation `Homotopic`, the present owner should use
that relation directly rather than store stronger directed homotopies as primitive fields. The
derived morphism-property API should therefore be attached to this owner rather than reintroduced
downstream as ad hoc wrappers. -/

/-- Definition 14.26.6: a homotopy equivalence between simplicial objects `U` and `V` consists of
a morphism `U ⟶ V`, a morphism `V ⟶ U`, and simplicial homotopies from the two composites to the
corresponding identity morphisms. -/
@[ext]
structure HomotopyEquiv (U V : SimplicialObject C) where
  /-- The forward morphism of a simplicial homotopy equivalence. -/
  hom : U ⟶ V
  /-- The backward morphism of a simplicial homotopy equivalence. -/
  inv : V ⟶ U
  /-- The composite `U ⟶ V ⟶ U` is simplicially homotopic to `𝟙 U`. -/
  homotopyHomInvId : Homotopic (hom ≫ inv) (𝟙 U)
  /-- The composite `V ⟶ U ⟶ V` is simplicially homotopic to `𝟙 V`. -/
  homotopyInvHomId : Homotopic (inv ≫ hom) (𝟙 V)

variable (C) in
/-- The morphism property on simplicial objects given by simplicial homotopy equivalences. -/
def homotopyEquivalences : MorphismProperty (SimplicialObject C) :=
  fun U V a ↦ ∃ e : HomotopyEquiv U V, e.hom = a

/-- A morphism of simplicial objects is a homotopy equivalence if it is the forward morphism of
some simplicial homotopy equivalence. -/
abbrev IsHomotopyEquivalence {U V : SimplicialObject C} (a : U ⟶ V) : Prop :=
  homotopyEquivalences C a

namespace HomotopyEquiv

variable {U V : SimplicialObject C}

/-- Any simplicial object is homotopy equivalent to itself. -/
@[refl]
def refl (U : SimplicialObject C) : HomotopyEquiv U U where
  hom := 𝟙 U
  inv := 𝟙 U
  homotopyHomInvId := by simpa using (Homotopic.refl (𝟙 U : U ⟶ U))
  homotopyInvHomId := by simpa using (Homotopic.refl (𝟙 U : U ⟶ U))

/-- The type of homotopy self-equivalences of a simplicial object is inhabited by the identity
homotopy equivalence. -/
instance (U : SimplicialObject C) : Inhabited (HomotopyEquiv U U) :=
  ⟨refl U⟩

/-- Reversing the arrows of a simplicial homotopy equivalence gives one in the opposite
direction. -/
@[symm]
def symm {U V : SimplicialObject C} (e : HomotopyEquiv U V) : HomotopyEquiv V U where
  hom := e.inv
  inv := e.hom
  homotopyHomInvId := e.homotopyInvHomId
  homotopyInvHomId := e.homotopyHomInvId

/-- Being simplicially homotopy equivalent is a transitive relation. -/
@[trans]
def trans (e : HomotopyEquiv U V) {W : SimplicialObject C} (f : HomotopyEquiv V W) :
    HomotopyEquiv U W where
  hom := e.hom ≫ f.hom
  inv := f.inv ≫ e.inv
  homotopyHomInvId := by
    have h :
        Homotopic ((e.hom ≫ f.hom) ≫ (f.inv ≫ e.inv)) (e.hom ≫ e.inv) := by
      simpa [Category.assoc] using (f.homotopyHomInvId.postcomp e.inv).precomp e.hom
    exact h.trans e.homotopyHomInvId
  homotopyInvHomId := by
    have h :
        Homotopic ((f.inv ≫ e.inv) ≫ (e.hom ≫ f.hom)) (f.inv ≫ f.hom) := by
      simpa [Category.assoc] using (e.homotopyInvHomId.postcomp f.hom).precomp f.inv
    exact h.trans f.homotopyInvHomId

/-- An isomorphism of simplicial objects induces a simplicial homotopy equivalence. -/
def ofIso (e : U ≅ V) : HomotopyEquiv U V where
  hom := e.hom
  inv := e.inv
  homotopyHomInvId := by simpa using (Homotopic.refl (𝟙 U : U ⟶ U))
  homotopyInvHomId := by simpa using (Homotopic.refl (𝟙 V : V ⟶ V))

/-- The forward map of a simplicial homotopy equivalence is a simplicial homotopy-equivalence
morphism. -/
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    IsHomotopyEquivalence e.hom :=
  ⟨e, rfl⟩

end HomotopyEquiv

end CategoryTheory.SimplicialObject
