import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import stacks_proof.stacks_project.Chap13.Definition_13_6_7
import stacks_proof.stacks_project.Chap13.Lemma_13_13_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open scoped CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => Fil^f(𝒜)
local notation "KFilt" => HomotopyCategory FilF (ComplexShape.up ℤ)

section Instances

variable [Abelian (finiteFilteredObjectCat 𝒜)]

local instance finiteFilteredHasFiniteBiproducts : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

instance finiteFilteredHasBinaryBiproducts : HasBinaryBiproducts FilF :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _

noncomputable instance finiteFilteredHomotopyPretriangulated :
    Pretriangulated KFilt := by
  infer_instance

noncomputable instance finiteFilteredHomotopyIsTriangulated :
    IsTriangulated KFilt := by
  infer_instance

end Instances

/- Domain-style sampling for Definition `13.13.5`.
- primary domain: Verdier localizations of triangulated homotopy categories by acyclic subobjects;
- sampled owner declarations:
  `filteredAcyclic`,
  `ObjectProperty.trW`,
  `CategoryTheory.ObjectProperty.verdierQuotientHDiv`,
  `MorphismProperty.Q`,
  `Functor.q_isLocalization`;
- best owner abstraction: the filtered-acyclic object property `filteredAcyclic`, with
  quotient API supplied by the chapter Verdier-quotient owner `D / P` from
  `Definition 13.6.7`, together with the canonical quotient functor `P.trW.Q`;
- primitive data: the filtered acyclic object property `filteredAcyclic` and the ambient
  abelian structure on `Fil^f(𝒜)`, from which the needed biproduct and pretriangulated
  structures on `KFilt` are derived canonically in this file;
- derived API: the filtered derived category, the canonical quotient functor, and the localization
  fact for that functor;
- source/core/bridge triage:
  `source-facing`: the filtered derived category `DF(𝒜)`;
  `core/canonical`: `KFilt / (FAc(𝒜) : ObjectProperty KFilt)` and
    `((FAc(𝒜) : ObjectProperty KFilt).trW).Q`;
  `bridge/view`: the identification with localization at
    `filteredQuasiIso = filteredAcyclic.trW`.

This file therefore reuses the Chapter `13` filtered-acyclic owner together with the generic
Verdier quotient owner, instead of redeclaring the quotient functor or rebuilding the quotient
category structure by hand. -/

section Quotient

variable [Abelian (finiteFilteredObjectCat 𝒜)]

variable (𝒜) in
/-- Definition 13.13.5: the filtered derived category `DF(𝒜)` is the Verdier quotient of
`K(Fil^f(𝒜))` by the triangulated subcategory `FAc(𝒜)` of filtered acyclic complexes,
equivalently the localization at the filtered quasi-isomorphisms `FQis(𝒜)`. -/
@[stacks 05S2]
abbrev filteredDerivedCategory : Type (max u v) :=
  KFilt / (FAc(𝒜) : ObjectProperty KFilt)

scoped notation "DF(" A:arg ")" => filteredDerivedCategory A

variable (𝒜) in
/- Companion recall: the filtered derived category owner from Definition `13.13.5` is written
`DF(𝒜)`. -/
#check (DF(𝒜))

variable (𝒜) in
/- Companion recall: the canonical quotient functor to `DF(𝒜)` is the Verdier quotient functor
`(FAc(𝒜) : ObjectProperty KFilt).trW.Q`. -/
#check
  (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))

end Quotient

section Localization

variable [Abelian (finiteFilteredObjectCat 𝒜)]

/-- The canonical quotient functor `K(Fil^f(𝒜)) ⥤ DF(𝒜)` commutes with shifts. -/
noncomputable instance filteredDerivedQuotientFunctor_commShift :
    ((((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))).CommShift ℤ :=
  inferInstance

/-- The canonical quotient functor `K(Fil^f(𝒜)) ⥤ DF(𝒜)` is exact. -/
noncomputable instance filteredDerivedQuotientFunctor_isTriangulated :
    ((((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))).IsTriangulated :=
  inferInstance

/-- The canonical quotient functor `K(Fil^f(𝒜)) ⥤ DF(𝒜)` localizes at the filtered
quasi-isomorphisms. -/
instance filteredDerivedQuotientFunctor_isLocalization :
    Functor.IsLocalization
      (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))
      (FQis(𝒜) : MorphismProperty KFilt) := by
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso]
  simpa using
    (Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW) :
      Functor.IsLocalization
        (((FAc(𝒜) : ObjectProperty KFilt).trW.Q) : KFilt ⥤ DF(𝒜))
        ((FAc(𝒜) : ObjectProperty KFilt).trW))

end Localization

end CategoryTheory
