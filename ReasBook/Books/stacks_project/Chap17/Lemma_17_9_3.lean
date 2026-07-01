import Mathlib
import stacks_project.Chap17.Definition_17_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u v u'

/- Domain-style sampling for Lemma 17.9.3:
- primary domain: finite-type sheaves of modules over a sheaf of rings on a site;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `CategoryTheory.ObjectProperty.IsClosedUnderQuotients`,
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`,
  `Abelian.factorThruImage`;
- owner abstraction: the canonical owner predicate `SheafOfModules.IsFiniteType`, together with
  its `ObjectProperty` view;
- primitive data: local finite generating families, as provided by
  `SheafOfModules.IsFiniteType.exists_localGeneratorsData`;
- derived API: closure under quotients, images, and short exact extensions.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claims that finite-type modules are stable under images and
  extensions;
- `core/canonical`: the owner predicate `SheafOfModules.IsFiniteType` and its object-property
  packaging;
- `bridge/view`: the ringed-space specialization obtained by taking `R = (RingedSpace.ringCatSheaf X)`.

The file should therefore state the closure facts at the generic `SheafOfModules` owner layer,
with ringed spaces only as a specialization, rather than as parallel ringed-space-specific global
theorems. -/

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- The object-property view of finite-type sheaves of modules over `R`. -/
abbrev isFiniteType (R : Sheaf J RingCat.{u}) : ObjectProperty (SheafOfModules R) :=
  IsFiniteType

variable {ℱ 𝒢 : SheafOfModules R}

-- Proof sketch: choose local finite generating data for `ℱ`; on each member of the cover, apply
-- `GeneratingSections.ofEpi` to the given epimorphism, preserving finiteness of the index sets.
/-- Finite-type sheaves of modules are closed under quotients. -/
instance isFiniteType_isClosedUnderQuotients :
    (isFiniteType R).IsClosedUnderQuotients := by
  sorry

-- Proof sketch: in a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`, locally lift finite generators
-- of `ℱ₃` along the epimorphism and adjoin finite generators of `ℱ₁`; these jointly generate
-- `ℱ₂`.
/-- Finite-type sheaves of modules are closed under extensions. -/
instance isFiniteType_isClosedUnderExtensions :
    (isFiniteType R).IsClosedUnderExtensions := by
  sorry

/-- Lemma 17.9.3 (1): the image of a morphism from a finite-type sheaf of modules is again of
finite type. -/
theorem isFiniteType_image (φ : ℱ ⟶ 𝒢) [ℱ.IsFiniteType] :
    (Abelian.image φ).IsFiniteType := sorry

-- Proof sketch: this is exactly the extension-closure statement for the object property
-- attached to `SheafOfModules.IsFiniteType`.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.9.3 (2): in a short exact sequence of sheaves of modules, if the left and right terms
are of finite type, then the middle term is of finite type. -/
theorem isFiniteType_of_shortExact
    {ℱ₁ ℱ₂ ℱ₃ : SheafOfModules R}
    (f : ℱ₁ ⟶ ℱ₂) (g : ℱ₂ ⟶ ℱ₃) (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    [ℱ₁.IsFiniteType] [ℱ₃.IsFiniteType] :
    ℱ₂.IsFiniteType := by
  exact (isFiniteType R).prop_X₂_of_shortExact hS inferInstance inferInstance

end SheafOfModules
