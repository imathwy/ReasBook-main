import Mathlib
import StacksProject_2024.stacks_project.Chap13.Definition_13_13_5
import StacksProject_2024.stacks_project.Chap13.Lemma_13_26_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_26_10

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
/-- Helper for Lemma 13.26.11: a bounded-below filtered-injective target is local for filtered
quasi-isomorphisms. -/
private theorem filteredQuasiIso_isLocal_filteredInjectivePlus_target
    (I : CochainComplex.FilteredInjectivePlus 𝒜) :
    (FQis(𝒜) : MorphismProperty KFilt).isLocal ((QhFiltInj).obj I) := by
  -- Rewrite locality along the identification of filtered quasi-isomorphisms with the
  -- triangulated closure of filtered acyclics; the source-faithful locality input is the
  -- filtered analogue of Lemma `13.26.10`.
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso, ObjectProperty.isLocal_trW (FAc(𝒜))]
  simpa using CochainComplex.FilteredInjectivePlus.rightOrthogonal (𝒜 := 𝒜) I

/-- Helper for Lemma 13.26.11: a local object for a localization property receives the same
Hom-set from an object before and after localization. -/
private theorem map_bijective_of_isLocal
    {D : Type*} [Category D] {W : MorphismProperty KFilt} {Y : KFilt}
    (hY : W.isLocal Y) (L : KFilt ⥤ D) [L.IsLocalization W] (X : KFilt) :
    Function.Bijective (L.map : (X ⟶ Y) → _) := by
  refine ⟨?_, ?_⟩
  · intro f₁ f₂ hf
    rw [MorphismProperty.map_eq_iff_precomp L W] at hf
    obtain ⟨Z, s, hs, eq⟩ := hf
    exact (hY s hs).1 eq
  · intro g
    obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction L W g
    have := Localization.inverts L W φ.s φ.hs
    obtain ⟨α, hα⟩ := (hY φ.s φ.hs).2 φ.f
    refine ⟨α, ?_⟩
    rw [hφ, ← cancel_epi (L.map φ.s), MorphismProperty.RightFraction.map_s_comp_map,
      ← hα, Functor.map_comp]

/-- Lemma 13.26.11 (1): precomposition with a filtered quasi-isomorphism induces a bijection on
morphisms into a bounded-below complex whose terms are filtered injective. -/
theorem precomp_bijective_of_filteredQuasiIso_to_boundedBelow_termwiseFilteredInjective
    {K L : KFilt} (I : CochainComplex.FilteredInjectivePlus 𝒜) (α : K ⟶ L)
    (hα : (FQis(𝒜) : MorphismProperty KFilt) α) :
    Function.Bijective
      (fun β : L ⟶ (QhFiltInj).obj I ↦ α ≫ β) := by
  -- The source cone argument is packaged by locality of the target object.
  exact filteredQuasiIso_isLocal_filteredInjectivePlus_target (𝒜 := 𝒜) I α hα

-- Proof sketch: filtered quasi-isomorphisms are inverted by the canonical quotient functor, and a
-- local target object therefore has the same incoming Hom-set before and after localization.
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
        (FQis(𝒜) : MorphismProperty KFilt) := by
    rw [← filteredAcyclic_trW_eq_filteredQuasiIso]
    exact Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW)
  simpa using
    map_bijective_of_isLocal
      (W := (FQis(𝒜) : MorphismProperty KFilt))
      (Y := (QhFiltInj).obj I)
      (filteredQuasiIso_isLocal_filteredInjectivePlus_target (𝒜 := 𝒜) I)
      (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))
      L

end CategoryTheory
