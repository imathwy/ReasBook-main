import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap15.Lemma_15_92_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory
open CategoryTheory.ObjectProperty

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A)

local notation "IB" => I.map (algebraMap A B)

/- Domain-style sampling:
- primary domain: derived-complete full subcategories in derived module categories under change of
  rings;
- sampled owner-side declarations:
  `DerivedCategory.derivedCompleteObjectProperty`,
  `ObjectProperty.lift`,
  `CategoryTheory.isDerivedCompleteWithRespectTo_iff_restrictScalars`,
  `CategoryTheory.derivedTensorWithAlgebraAdjunction`;
- best owner abstraction: the source-facing equivalence lives on the full subcategories cut out by
  `derivedCompleteObjectProperty`, and the comparison functor is the canonical
  `ObjectProperty.lift` of derived restriction of scalars;
- primitive data: the ideal `I`, the flat algebra map `A → B`, and the canonical derived
  restriction functor `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- derived API: the induced equivalence
  `D_comp(B, IB) ⥤ D_comp(A, I)`.

Layer triage:
- `source-facing`: the equivalence between the derived-complete full subcategories;
- `core/canonical`: `derivedCompleteObjectProperty` together with `ObjectProperty.lift`;
- `bridge/view`: `isDerivedCompleteWithRespectTo_iff_restrictScalars` and
  `derivedTensorWithAlgebraAdjunction`. -/

-- Proof sketch: Lemma `15.92.24` shows that restriction lands in the derived-complete full
-- subcategory. For essential surjectivity, use the Stacks construction
-- `K ↦ RHom_A(B, K)` from the source proof, realized through the derived change-of-rings
-- adjunction of Lemma `15.60.3`; the flatness and quotient-bijectivity hypotheses together with
-- Lemma `15.90.4` make the unit and counit become isomorphisms on the derived-complete
-- subcategories.
/-- Lemma 15.92.25: if `A → B` is flat, `I ⊆ A` is finitely generated, and the canonical quotient
map `A / I → B / I B` is bijective, then the restriction functor `D(B) ⥤ D(A)` induces an
equivalence from the full subcategory `D_{comp}(B, I B)` of `IB`-derived-complete complexes to the
full subcategory `D_{comp}(A, I)` of `I`-derived-complete complexes. -/
theorem derivedCompleteRestriction_isEquivalence_of_flat_of_quotientMap_bijective
    [Module.Flat A B] (hI : I.FG)
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          IB
          (algebraMap A B)
          Ideal.le_comap_map)) :
    Functor.IsEquivalence
      ((derivedCompleteObjectProperty I).lift
        ((derivedCompleteObjectProperty IB).ι ⋙
          (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory)
        (fun L ↦ (isDerivedCompleteWithRespectTo_iff_restrictScalars L.obj I).2 L.property)) :=
  sorry

end

end CategoryTheory
