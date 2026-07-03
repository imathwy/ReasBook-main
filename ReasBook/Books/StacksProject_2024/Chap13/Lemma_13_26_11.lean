import Mathlib
import StacksProject_2024.Chap13.Definition_13_13_5
import StacksProject_2024.Chap13.Lemma_13_26_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open ComplexShape
open FilteredObject
open scoped CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "QhFilt" => HomotopyCategory.quotient FilF (up ℤ)
local notation "KFilt" => HomotopyCategory FilF (up ℤ)
local notation "QhFiltInj" =>
  CochainComplex.PlusWithTermsIn.ι (IsFilteredInjective : ObjectProperty FilF) ⋙ QhFilt

local instance finiteFiltered_hasFiniteBiproducts_13_26_11 : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance finiteFiltered_hasBinaryBiproducts_13_26_11 : HasBinaryBiproducts FilF :=
  CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts _

local instance pretriangulated_filtered_homotopy_13_26_11 :
    Pretriangulated KFilt := by
  exact HomotopyCategory.instPretriangulatedIntUp FilF

local instance isTriangulated_filtered_homotopy_13_26_11 : IsTriangulated KFilt := inferInstance

/- Domain-style sampling for Lemma `13.26.11`.
- primary domain: Verdier localization of the filtered homotopy category at filtered
  quasi-isomorphisms, together with the filtered analogue of bounded-below injective cochain
  complexes and right orthogonality against filtered acyclic objects;
- sampled owner declarations in this domain:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.PlusWithTermsIn.plus`,
  `CochainComplex.PlusWithTermsIn.term_mem`,
  `CochainComplex.FilteredInjectivePlus.rightOrthogonal`,
  `ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`,
  `DF(𝒜)`;
- best owner abstraction: the filtered analogue
  `CochainComplex.FilteredInjectivePlus 𝒜` of `CochainComplex.InjectivePlus 𝒜`, which packages
  bounded-belowness together with termwise filtered injectivity, while the canonical quotient
  functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))` remains the localization
  bridge;
- primitive data: a filtered quasi-isomorphism `α` in `KFilt`, together with a bounded-below
  filtered-injective target `I : CochainComplex.FilteredInjectivePlus 𝒜`;
- derived API: bijectivity of precomposition in `KFilt` and bijectivity of the localization map on
  morphisms into that target;
- source/core/bridge triage:
  `source-facing`: the two bijectivity statements below;
  `core/canonical`: `CochainComplex.FilteredInjectivePlus`, `ObjectProperty.rightOrthogonal`,
    `DF(𝒜)`, and `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`;
  `bridge/view`: the textbook null-homotopy statement of Lemma `13.26.10`, derived from the owner
  theorem `CochainComplex.FilteredInjectivePlus.rightOrthogonal`.

This file therefore keeps the source-facing statements, but refines the target hypothesis from a
raw bounded-below cochain complex with separate termwise filtered-injectivity hypotheses to the
owner `CochainComplex.FilteredInjectivePlus 𝒜`, and writes theorem `(2)` directly with the
canonical quotient functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`. -/

-- Proof sketch: the owner theorem
-- `CochainComplex.FilteredInjectivePlus.rightOrthogonal` places the target object
-- in the right orthogonal of `FAc(𝒜)`. Since `FQis(𝒜) = (FAc(𝒜)).trW` by Lemma `13.13.4`, the
-- canonical theorem
-- `ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated` applied to the chapter owner
-- functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))` gives bijectivity of
-- precomposition with `α`.
/-- Lemma 13.26.11 (1): precomposition with a filtered quasi-isomorphism induces a bijection on
morphisms into a bounded-below complex whose terms are filtered injective. -/
theorem precomp_bijective_of_filteredQuasiIso_to_boundedBelow_termwiseFilteredInjective
    {K L : KFilt} (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ L)
    (hα : (FQis(𝒜) : MorphismProperty KFilt) α) :
    Function.Bijective
      (fun β : L ⟶ (QhFiltInj).obj I ↦ α ≫ β) := by
  have hY : (FQis(𝒜) : MorphismProperty KFilt).isLocal ((QhFiltInj).obj I) := by
    rw [← filteredAcyclic_trW_eq_filteredQuasiIso, ObjectProperty.isLocal_trW (FAc(𝒜))]
    exact I.rightOrthogonal
  exact hY α hα

-- Proof sketch: any morphism in the localization is represented by a right fraction whose
-- denominator is a filtered quasi-isomorphism. Part (1) lets one descend the numerator to a map
-- from `L` to `I`, giving surjectivity; applying part (1) again to a denominator that kills a map
-- in the localization gives injectivity.
/-- Lemma 13.26.11 (2): for a bounded-below complex whose terms are filtered injective, the
canonical map from the filtered homotopy category to the filtered derived category identifies
morphisms into it in `K(Fil^f(𝒜))` with morphisms into it in `DF(𝒜)`. -/
theorem homotopyCategory_to_filteredDerived_bijective_of_boundedBelow_termwiseFilteredInjective
    (L : KFilt) (I : CochainComplex.FilteredInjectivePlus 𝒜) :
    Function.Bijective
      ((((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜)).map :
        (L ⟶ (QhFiltInj).obj I) → _) := by
  letI :
      Functor.IsLocalization
        (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))
        ((FAc(𝒜) : ObjectProperty KFilt).trW) := by
    exact Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW)
  simpa using
    (I.rightOrthogonal).map_bijective_of_isTriangulated
      (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜)) L

end CategoryTheory
