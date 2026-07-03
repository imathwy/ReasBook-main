import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/- Domain-style sampling for Definition 12.21.1:
- primary domain: exact couples and their page-one differential objects in a category with zero
  morphisms;
- sampled canonical declarations in the surrounding owner ecosystem:
  `ShortComplex`,
  `ShortComplex.Exact`,
  `HomologicalComplex C (ComplexShape.refl PUnit)`,
  `HomologicalComplex.sc`;
- best owner abstraction for the page-level differential data: the chapter owner
  `HomologicalComplex C (ComplexShape.refl PUnit)`;
- primitive data: the triangle objects `A`, `E`, the maps `α`, `f`, `g`, the three zero
  composites, and the three exactness assertions;
- derived API: the differential `d = f ≫ g` and the one-object page complex obtained from the
  canonical homological-complex owner;
- source/core/bridge triage:
  `source-facing`: `ExactCouple`;
  `core/canonical`: `ShortComplex` exactness and the owner type
  `HomologicalComplex C (ComplexShape.refl PUnit)`;
  `bridge/view`: `ExactCouple.page`.

The structure `ExactCouple` is the source-facing owner, while the page-level differential object is
only a bridge to the chapter's existing one-object homological-complex owner. -/
/-- Definition 12.21.1: an exact couple consists of objects `A` and `E` with morphisms
`α : A ⟶ A`, `f : E ⟶ A`, and `g : A ⟶ E` such that the three cyclic pairs `f, α`, `g, f`,
and `α, g` are exact. For the textbook abelian-category notion, the ambient abelian hypothesis
is only needed by downstream constructions using images, kernels, and homology, not by this
source-facing owner itself. -/
structure ExactCouple where
  /-- The `A`-object of the exact couple. -/
  A : C
  /-- The `E`-object of the exact couple. -/
  E : C
  /-- The endomorphism `α : A ⟶ A` in the exact-couple triangle. -/
  α : A ⟶ A
  /-- The morphism `f : E ⟶ A` in the exact-couple triangle. -/
  f : E ⟶ A
  /-- The morphism `g : A ⟶ E` in the exact-couple triangle. -/
  g : A ⟶ E
  /-- The composite `f ≫ α` vanishes. -/
  f_comp_α : f ≫ α = 0
  /-- The composite `g ≫ f` vanishes. -/
  g_comp_f : g ≫ f = 0
  /-- The composite `α ≫ g` vanishes. -/
  α_comp_g : α ≫ g = 0
  /-- Exactness of `E ⟶ A ⟶ A`, expressing `ker(α) = im(f)`. -/
  exact_f_α : (ShortComplex.mk f α f_comp_α).Exact
  /-- Exactness of `A ⟶ E ⟶ A`, expressing `ker(f) = im(g)`. -/
  exact_g_f : (ShortComplex.mk g f g_comp_f).Exact
  /-- Exactness of `A ⟶ A ⟶ E`, expressing `ker(g) = im(α)`. -/
  exact_α_g : (ShortComplex.mk α g α_comp_g).Exact

namespace ExactCouple

local notation "ExactCoupleCat" => @ExactCouple C _ _

variable (X : @ExactCouple C _ _)

/-- The differential on the middle object of an exact couple. -/
abbrev d : X.E ⟶ X.E :=
  X.f ≫ X.g

/-- The differential of an exact couple squares to zero. -/
@[simp]
theorem d_comp_d : X.d ≫ X.d = 0 := by
  simpa [d, Category.assoc] using congrArg (fun k ↦ X.f ≫ k ≫ X.g) X.g_comp_f

/-- Bridge/view layer: an exact couple carries the canonical one-object homological complex on its
middle object, with differential `d = f ≫ g`. -/
instance : CoeOut ExactCoupleCat (HomologicalComplex C (ComplexShape.refl PUnit.{1})) where
  coe X :=
    { X := fun _ ↦ X.E
      d := fun _ _ ↦ X.d
      shape := fun _ _ h ↦ False.elim (h rfl)
      d_comp_d' := fun _ _ _ _ _ ↦ X.d_comp_d }

/-- The one-object homological complex carried by the middle object of an exact couple. -/
abbrev page : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  X

end ExactCouple

end

end CategoryTheory
