import Mathlib
import StacksProject_2024.Chap13.Lemma_13_19_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open CochainComplex.HomComplex.CohomologyClass

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

namespace CochainComplex

/- Domain-style sampling:
- primary domain: bounded-above projective cochain complexes in an abelian category and their
  derived-category `Ext` computation via shifted morphisms;
- sampled owner declarations:
  `ShiftedHom`,
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `DerivedCategory.Q.commShiftIso`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`;
- best owner abstraction: the source-side bounded-above/projective owner is
  `CochainComplex.ProjectiveMinus 𝒜`; its canonical bridge to the derived category is the Chapter
  13 owner theorem
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`, while
  `ShiftedHom (Q.obj P) (Q.obj L) n` is the canonical shifted-Hom owner on the derived-category
  side;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(Hom^•(P^•, L^•)) ≃ Hom_D(P^•, L^•[n])`;
  `core/canonical`: `ProjectiveMinus`, `Qh.mapAddHom`, `Q.commShiftIso`, and `ShiftedHom`;
  `bridge/view`: the direct composite from Hom-complex cohomology classes to homotopy morphisms,
  then to derived morphisms out of the owner `ProjectiveMinus 𝒜`.

This file should therefore keep only the source-facing bridge at the abelian-category owner level,
not a duplicate projective-resolution wrapper around the same owner data. -/

namespace ProjectiveMinus

/-- Helper for Lemma 15.74.2: transport of morphisms across isomorphisms is additive in a
preadditive category. -/
private lemma iso_homCongr_map_add
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁)
    (f g : X ⟶ Y) :
    α.homCongr β (f + g) = α.homCongr β f + α.homCongr β g := by
  -- Additivity is exactly bilinearity of composition applied to `Iso.homCongr`.
  simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Helper for Lemma 15.74.2: an isomorphism on source and target induces an additive
equivalence on the corresponding Hom groups. -/
private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := iso_homCongr_map_add α β

/-- Helper for Lemma 15.74.2: homotopy morphisms from a bounded-above projective complex into a
shifted complex identify additively with shifted derived morphisms. -/
private noncomputable def homotopyShiftedHomAddEquiv
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) (n : ℤ) :
    ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) ≃+ ShiftedHom (Q.obj P) (Q.obj L) n :=
  -- First pass from the homotopy category to the derived category using projectivity of `P`.
  (AddEquiv.ofBijective
      (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) →+ _)
      (homotopyCategory_to_derived_bijective_of_boundedAbove_projective P (L⟦n⟧))).trans
    -- Then transport the target across the canonical shift-commutation isomorphism for `Q`.
    (isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso n).app L))

/-- Lemma 15.74.2: if `P^•` is a bounded-above cochain complex of projective objects in an
abelian category `𝒜` and `L^•` is any cochain complex in `𝒜`, then the complex
`Hom^•(P^•, L^•)` computes the derived Hom from `P^•` to shifts of `L^•`; in degree `n` its
cohomology identifies with morphisms `P^• ⟶ L^•[n]` in the derived category `D(𝒜)` as an
additive equivalence. This is exactly the canonical composite of the Hom-complex cohomology
bridge, the owner bijectivity theorem for `ProjectiveMinus 𝒜`, and the derived shift
identification. -/
noncomputable def homologyAddEquivShiftedHom
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) (n : ℤ) :
    (HomComplex P L).homology n ≃+ ShiftedHom (Q.obj P) (Q.obj L) n
  :=
  -- The source-side cohomology classes already identify with homotopy morphisms.
  ((HomComplex.homologyAddEquiv P L n).trans homAddEquiv).trans
    -- Compose that with the projective-minus comparison to derived shifted morphisms.
    (homotopyShiftedHomAddEquiv P L n)

end ProjectiveMinus

end CochainComplex

end
