import Mathlib
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_13_13_1 (from Chap13) -/
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [HasZeroObject 𝒜]

/- Domain-style sampling for Definition 13.13.1:
- primary domain: filtered objects in a category with zero object and the full subcategory cut out
  by the finiteness predicate on filtrations;
- sampled owner declarations:
  `FilteredObject`,
  `FilteredObject.IsFinite`,
  `FilteredObject.forget`,
  `FilteredObject.associatedGradedFunctor`,
  `FullSubcategory`,
  `ι`;
- owner abstraction: the source-facing owner for this item is the full subcategory
  `finiteFilteredObjectCat 𝒜`, built canonically as
  `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).FullSubcategory`;
- source/core/bridge triage:
  `source-facing`: the category `Fil^f(𝒜)` of finite filtered objects;
  `core/canonical`: `FilteredObject 𝒜` together with the generic owner
    `(FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))).FullSubcategory`;
  `bridge/view`: the notation `Fil^f(𝒜)` for that full subcategory.

Primitive data versus derived API:
- primitive data: the ambient filtered-object owner `FilteredObject 𝒜` and the finiteness
  predicate `FilteredObject.IsFinite`;
-- derived API: the full subcategory owner `finiteFilteredObjectCat 𝒜` and the textbook notation
  `Fil^f(𝒜)`, together with the canonical forgetful and associated-graded functors obtained by
  restricting `FilteredObject.forget` and `FilteredObject.associatedGradedFunctor` along the
  full-subcategory inclusion;
-- no parallel inclusion wrapper is kept: the canonical inclusion is used directly as
  `ι : Fil^f(𝒜) ⥤ Fil(𝒜)`.

This item is therefore `source-facing`, not a recall-only bridge: Definition `13.13.1` is the
right owner file for the finite filtered category itself, while later files should reuse this owner
rather than re-declare it. -/

/-- Definition 13.13.1: for a category `𝒜` with zero object, the category of finite filtered
objects is the full subcategory of `FilteredObject 𝒜` on objects whose filtration is finite. -/
abbrev finiteFilteredObjectCat (𝒜 : Type u) [Category.{v} 𝒜] [HasZeroObject 𝒜] :=
  ObjectProperty.FullSubcategory (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))

/- The Stacks Project writes the category of finite filtered objects as `Fil^f(𝒜)`. This is
notation for the source-facing owner `finiteFilteredObjectCat 𝒜`. -/
scoped notation "Fil" "^f" "(" C ")" => finiteFilteredObjectCat C

/- Companion recall: no separate `finiteFilteredObjectInclusion` wrapper is introduced here; the
canonical inclusion `Fil^f(𝒜) ⥤ Fil(𝒜)` is used directly as the object-property inclusion
`ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜)))`. -/
#check
  (ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) :
    Fil^f(𝒜) ⥤ Fil(𝒜))

/- Companion check: the Stacks notation `Fil^f(𝒜)` is this recalled owner. -/
#check (Fil^f(𝒜))

instance : ObjectProperty.ContainsZero (FilteredObject.IsFinite : ObjectProperty (Fil(𝒜))) where
  exists_zero := by
    letI : HasZeroMorphisms 𝒜 := by
      exact HasZeroObject.zeroMorphismsOfZeroObject (C := 𝒜)
    letI : Subsingleton (Subobject ((0 : Fil(𝒜)).obj)) :=
      Subobject.subsingleton_of_isZero
        ((FilteredObject.forget : Fil(𝒜) ⥤ 𝒜).map_isZero (isZero_zero _))
    refine ⟨0, isZero_zero _, ?_⟩
    exact ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

instance : HasZeroObject (Fil^f(𝒜)) :=
  inferInstance

section RestrictionFunctors

variable (C : Type u) [Category.{v} C] [HasZeroObject C]

/-- The canonical forgetful functor from finite filtered objects to the ambient category. -/
abbrev finiteFilteredObjectForgetFunctor : Fil^f(C) ⥤ C :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(C))) ⋙ FilteredObject.forget

/-- The canonical associated-graded functor on finite filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedFunctor [HasZeroMorphisms C] [HasCokernels C] :
    Fil^f(C) ⥤ GradedObject ℤ C :=
  ObjectProperty.ι (FilteredObject.IsFinite : ObjectProperty (Fil(C))) ⋙
    FilteredObject.associatedGradedFunctor

/-- The termwise associated-graded functor on cochain complexes of finite filtered objects. -/
abbrev finiteFilteredObjectAssociatedGradedCochainFunctor [HasZeroMorphisms C] [HasCokernels C] :
    CochainComplex (finiteFilteredObjectCat C) ℤ ⥤ CochainComplex (GradedObject ℤ C) ℤ :=
  (finiteFilteredObjectAssociatedGradedFunctor C).mapHomologicalComplex (ComplexShape.up ℤ)

end RestrictionFunctors

end CategoryTheory

/-! ### Definition_13_13_2 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open HomotopyCategory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KFilt" => HomotopyCategory (Fil^f(𝒜)) (up ℤ)

/- Domain-style sampling for Definition `13.13.2`.
- primary domain: filtered complexes in the homotopy category and their associated graded images;
- sampled owner declarations in this domain:
  `finiteFilteredObjectCat 𝒜`,
  `FilteredObject.associatedGradedFunctor`,
  `Functor.mapHomotopyCategory`,
  `HomotopyCategory.quasiIso`,
  `HomotopyCategory.subcategoryAcyclic`;
- best owner abstraction: the source-facing bridge functor from `K(Fil^f(𝒜))` to `K(Gr(𝒜))`
  induced by the associated graded functor on filtered objects, together with the canonical
  homotopy-category owners `HomotopyCategory.quasiIso` and
  `HomotopyCategory.subcategoryAcyclic` on the target;
- primitive data: the finite-filtered full-subcategory owner and the canonical associated-graded
  functor on filtered objects;
- derived API: the associated-graded homotopy functor and its inverse-image morphism and object
  properties on `K(Fil^f(𝒜))`;
- ambient structure check: the target graded category `GradedObject ℤ 𝒜` is already abelian
  upstream from `[Abelian 𝒜]`, so no separate file-scope assumption
  `[Abelian (GradedObject ℤ 𝒜)]` belongs in this local API;
- source/core/bridge triage:
  `source-facing`: the Stacks notations `FQis(𝒜)` and `FAc(𝒜)` on `K(Fil^f(𝒜))`;
  `core/canonical`: `HomotopyCategory.quasiIso` and `HomotopyCategory.subcategoryAcyclic`;
  `bridge/view`: the associated-graded homotopy functor from `K(Fil^f(𝒜))` to `K(Gr(𝒜))`.

This file therefore owns the associated-graded homotopy bridge used to define the Stacks
properties, so later files can reuse that bridge directly instead of redeclaring the same functor
under a second chapter-level name. -/

variable (𝒜) in
/-- The associated graded functor induced on the homotopy category of finite filtered objects. -/
abbrev filteredAssociatedGradedHomotopyFunctor :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) :=
  (finiteFilteredObjectAssociatedGradedFunctor 𝒜).mapHomotopyCategory (up ℤ)

/-
Definition 13.13.2 (1): the morphism property of filtered quasi-isomorphisms on the homotopy
category of finite filtered complexes.
-/
variable (𝒜) in
/-- Definition 13.13.2 (1): the owner morphism property of filtered quasi-isomorphisms on the
homotopy category of finite filtered complexes. -/
abbrev filteredQuasiIso : MorphismProperty KFilt :=
  (quasiIso (GradedObject ℤ 𝒜) (up ℤ)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FQis(" A:arg ")" => filteredQuasiIso A

/-
Definition 13.13.2 (2): the object property of filtered acyclic complexes on the homotopy
category of finite filtered complexes.
-/
variable (𝒜) in
/-- Definition 13.13.2 (2): the owner object property of filtered acyclic complexes on the
homotopy category of finite filtered complexes. -/
abbrev filteredAcyclic : ObjectProperty KFilt :=
  (subcategoryAcyclic (GradedObject ℤ 𝒜)).inverseImage
    (filteredAssociatedGradedHomotopyFunctor 𝒜)

scoped notation "FAc(" A:arg ")" => filteredAcyclic A

/- Companion checks: the associated-graded homotopy bridge and the Stacks notations `FQis(𝒜)` and
`FAc(𝒜)` are the canonical public owners used in later files. -/
#check
  (filteredAssociatedGradedHomotopyFunctor 𝒜 :
    KFilt ⥤ HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))
#check (filteredQuasiIso 𝒜 : MorphismProperty KFilt)
#check (filteredAcyclic 𝒜 : ObjectProperty KFilt)
#check (FQis(𝒜) : MorphismProperty KFilt)
#check (FAc(𝒜) : ObjectProperty KFilt)

end CategoryTheory

/-! ### Lemma_13_13_3 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.3`.
- primary domain: homological functors out of the homotopy category of finite filtered objects;
- sampled core/canonical declarations in this domain:
  `finiteFilteredObjectAssociatedGradedFunctor`,
  `filteredAssociatedGradedHomotopyFunctor`,
  `finiteFilteredObjectForgetFunctor`,
  `HomotopyCategory.homologyFunctor`;
- best owner abstraction: the owner is the canonical `Functor.IsHomological` instance on composites
  into degree-zero homology, together with the owner instances
  `Functor.CommShift` and `Functor.IsTriangulated` for `mapHomotopyCategory`;
- primitive data: the canonical associated-graded and forgetful functors from Definitions
  `13.13.1` and `13.13.2`;
- derived API: the three homologicality facts for `H^0 ∘ gr`, `H^0 ∘ gr^p`, and
  `H^0 ∘ forget`.

Source/core/bridge triage:
- `source-facing`: the three homologicality statements in Lemma `13.13.3`;
- `core/canonical`: `Functor.CommShift`, `Functor.IsTriangulated`, and
  `Functor.IsHomological`;
- `bridge/view`: `filteredAssociatedGradedHomotopyFunctor 𝒜`,
  `(GradedObject.eval p).mapHomotopyCategory (up ℤ)`, and
  `(finiteFilteredObjectForgetFunctor 𝒜).mapHomotopyCategory (up ℤ)`.

This item is therefore a pure canonical-recall file: after supplying the ordinary finite/binary
biproduct support on `Fil^f(𝒜)`, mathlib already infers the needed `CommShift`,
`IsTriangulated`, and `IsHomological` structures, so no parallel public wrapper declarations
belong here. -/

section Homologicality

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "Hzero" => HomotopyCategory.homologyFunctor 𝒜 (up ℤ) 0

local instance : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance : HasBinaryBiproducts FilF :=
  hasBinaryBiproducts_of_finite_biproducts FilF

/-- Lemma 13.13.3: the functor `K(Fil^f(𝒜)) ⥤ Gr(𝒜)` sending `K^•` to `H^0(gr(K^•))` is
homological. -/
instance filteredAssociatedGraded_homologyZero_isHomological :
    (filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
      HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0).IsHomological := by
  -- The source proof factors through exactness of `gr` and homologicality of `H^0`.
  infer_instance

/-- Helper for Lemma 13.13.3: for each `p : ℤ`, the functor sending `K^•` to `H^0(gr^p(K^•))`
is homological. -/
instance filteredGradedPiece_homologyZero_isHomological (p : ℤ) :
    (filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
      (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙ Hzero).IsHomological := by
  -- This specializes the graded homologicality statement along evaluation at degree `p`.
  infer_instance

/-- Helper for Lemma 13.13.3: the functor sending `K^•` to `H^0((forget F)K^•)` is homological. -/
instance filteredForget_homologyZero_isHomological :
    ((finiteFilteredObjectForgetFunctor 𝒜 : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ) ⋙
      Hzero).IsHomological := by
  -- This is the forgetful exact functor composed with the standard degree-zero homology functor.
  infer_instance

end Homologicality

end CategoryTheory

/-! ### Lemma_13_13_4 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open scoped CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "KFilt" => HomotopyCategory FilF (ComplexShape.up ℤ)

local instance finiteFiltered_hasFiniteBiproducts_13_13_4 : HasFiniteBiproducts FilF :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance finiteFiltered_hasBinaryBiproducts_13_13_4 : HasBinaryBiproducts FilF :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _

local notation "H0gr" =>
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) 0

local instance filteredAssociatedGradedZeroHomology_isHomological :
    (H0gr).IsHomological := by
  infer_instance

/- Domain-style sampling for Lemma `13.13.4`.
- primary domain: triangulated localizations defined by the homological kernel of a homological
  functor on a homotopy category;
- sampled owner declarations in this domain:
  `filteredAssociatedGradedHomotopyFunctor 𝒜`,
  `HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0`,
  `Functor.homologicalKernel`,
  `ObjectProperty.trW`,
  `MorphismProperty.Q`;
- best owner abstraction: the canonical homological-kernel owner
  `((filteredAssociatedGradedHomotopyFunctor 𝒜) ⋙
    HomotopyCategory.homologyFunctor (GradedObject ℤ 𝒜) (up ℤ) 0).homologicalKernel`,
  together with its derived Verdier morphism property and localization functor;
- primitive data: the canonical composite `H^0 ∘ gr` built from
  `filteredAssociatedGradedHomotopyFunctor 𝒜` and the degree-zero homology functor;
- derived API: its homological kernel, the induced morphism property `.trW`, and the localization
  functor `.Q`;
- source/core/bridge triage:
  `source-facing`: the filtered acyclic object property `FAc(𝒜)` and the filtered
    quasi-isomorphism property `FQis(𝒜)`;
  `core/canonical`: `Functor.homologicalKernel`, `ObjectProperty.trW`, and `MorphismProperty.Q`;
  `bridge/view`: the identifications in this file between `FAc(𝒜)`, `FQis(𝒜)`, and the canonical
    homological-kernel localization package.

This file therefore keeps the source-facing `FAc(𝒜)`/`FQis(𝒜)` statements while using the
canonical composite `H^0 ∘ gr` directly, without any parallel local wrapper around that owner or
around the localization functor `(FQis(𝒜) : MorphismProperty KFilt).Q`. The only inverted-morphism
input needed below is the canonical bridge
`Functor.homologicalKernel_trW_isInvertedBy` from Lemma `13.6.11`. -/

/-- The filtered acyclic objects are exactly the homological kernel of `H^0 ∘ gr`. -/
theorem filteredAcyclic_eq_homologicalKernel :
    (FAc(𝒜) : ObjectProperty KFilt) = (H0gr).homologicalKernel :=
  sorry

/-- The Verdier morphism property of filtered acyclic objects is the filtered quasi-isomorphism
property. -/
theorem filteredAcyclic_trW_eq_filteredQuasiIso :
    (FAc(𝒜) : ObjectProperty KFilt).trW =
      (FQis(𝒜) : MorphismProperty KFilt) := sorry

/-- Lemma 13.13.4 (1): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is strictly full. -/
instance filteredAcyclic_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

/-- Lemma 13.13.4 (2): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is saturated. -/
instance filteredAcyclic_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

/-- Lemma 13.13.4 (3): the full subcategory `FAc(𝒜)` of `K(Fil^f(𝒜))` consisting of filtered
acyclic complexes is triangulated. -/
instance filteredAcyclic_isTriangulated :
    ObjectProperty.IsTriangulated
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

/-- Lemma 13.13.4 (4): the corresponding saturated multiplicative system of
`K(Fil^f(𝒜))` is the set `FQis(𝒜)` of filtered quasi-isomorphisms. -/
instance filteredQuasiIso_isSaturatedMultiplicativeSystem :
    IsSaturatedMultiplicativeSystem (FQis(𝒜) : MorphismProperty KFilt) := by
  sorry

-- Proof sketch: apply Lemma `13.6.10` to the triangulated subcategory
-- `FAc(𝒜) = (H^0 ∘ gr).homologicalKernel`, whose associated
-- multiplicative system is by definition `FQis(𝒜)`.
/-- Lemma 13.13.4 (5): the kernel of the localization functor
`Q : K(Fil^f(𝒜)) ⥤ FQis(𝒜)⁻¹K(Fil^f(𝒜))` is `FAc(𝒜)`. -/
theorem kernel_filteredQuasiIsomorphismLocalizationFunctor :
    Functor.kernel
        (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
            (FQis(𝒜) : MorphismProperty KFilt).Localization) =
      (FAc(𝒜) : ObjectProperty KFilt) := by
  sorry

-- Proof sketch: the canonical composite `H^0 ∘ gr` is homological by
-- Lemma `13.13.3`, so `Functor.mem_homologicalKernel_trW_iff` shows that the canonical
-- morphism property `((H^0 ∘ gr).homologicalKernel).trW` is inverted. The required factorization
-- is then the direct canonical localization lift through the quotient functor
-- `(FQis(𝒜) : MorphismProperty KFilt).Q`.
/-- Lemma 13.13.4 (6): the functor `H^0 ∘ gr` factors through the localization functor
`Q : K(Fil^f(𝒜)) ⥤ FQis(𝒜)⁻¹K(Fil^f(𝒜))`. -/
theorem exists_filteredGradedZeroHomologyFunctor_factorization :
    ∃ H' :
        (FQis(𝒜) : MorphismProperty KFilt).Localization ⥤
          GradedObject ℤ 𝒜,
      (((FQis(𝒜) : MorphismProperty KFilt).Q) :
          KFilt ⥤
        (FQis(𝒜) : MorphismProperty KFilt).Localization) ⋙
          H' =
        H0gr := by
  sorry

end CategoryTheory

/-! ### Definition_13_13_5 (from Chap13) -/
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

/-! ### Lemma_13_13_6 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open scoped CategoryTheory

universe u v

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.6`.
- primary domain: filtered derived associated-graded functors and the passage from
  `D(Gr(\mathcal A))` to graded objects in `D(\mathcal A)`;
- sampled owner declarations:
  `filteredAssociatedGradedHomotopyFunctor`,
  `filteredDerivedCategory`,
  `Localization.lift`,
  `Functor.mapDerivedCategory`,
  `GradedObject.eval`;
- best owner abstraction: the descended associated-graded functor
  `DF(\mathcal A) ⥤ D(Gr(\mathcal A))` together with its direct descended graded-piece functors
  `gr^p : DF(\mathcal A) ⥤ D(\mathcal A)`, each defined as the localization lift of the
  homotopy-level `gr^p`; the bundled bridge `DF(\mathcal A) ⥤ Gr(D(\mathcal A))` is only a
  companion view obtained from `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))`;
- primitive data: the homotopy-level associated-graded owner
  `filteredAssociatedGradedHomotopyFunctor 𝒜`, the homotopy-level graded-piece functors, the
  canonical quotient functor `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt)`, and the
  localization lifts of
  these source-facing functors;
- derived API: the bridge functor to `Gr(D(\mathcal A))`, the comparison isomorphism between its
  degree-`p` evaluation and the direct descended `gr^p`, and the exactness data for the
  source-facing lifts;
- source/core/bridge triage:
  `source-facing`: the descended associated-graded functor on `DF(\mathcal A)` and the direct
    descended `p`-th graded-piece functors;
  `core/canonical`: `filteredDerivedCategory`,
    `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt)`,
    `Localization.lift`, `Functor.mapDerivedCategory`, and `GradedObject.eval`;
  `bridge/view`: the comparison functor `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))` and the bundled
    graded-object-valued packaging of the direct `gr^p`.

This file therefore keeps the localization lift to `D(Gr(\mathcal A))` as the source-facing
descended `gr`, defines the descended `gr^p` directly by localization, and treats
`DF(\mathcal A) ⥤ Gr(D(\mathcal A))` only as a companion bridge/view. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]
variable [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (up ℤ)
local notation "DFilt" => filteredDerivedCategory 𝒜
local notation "DGr" => DerivedCategory (GradedObject ℤ 𝒜)

private abbrev QFilt : KFilt ⥤ DFilt :=
  (((FAc(𝒜) : ObjectProperty KFilt).trW).Q : KFilt ⥤ DFilt)

instance qFilt_isLocalization :
    Functor.IsLocalization QFilt (FQis(𝒜) : MorphismProperty KFilt) := by
  rw [← filteredAcyclic_trW_eq_filteredQuasiIso]
  simpa [QFilt] using
    (Functor.q_isLocalization ((FAc(𝒜) : ObjectProperty KFilt).trW) :
      Functor.IsLocalization
        (((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DFilt))
        ((FAc(𝒜) : ObjectProperty KFilt).trW))

private noncomputable instance filteredDerived_shift_additive
    [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))] (n : ℤ) :
    (shiftFunctor DFilt n).Additive := by
  infer_instance

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]

/-- The associated graded functor from `K(Fil^f(\mathcal A))` to `D(Gr(\mathcal A))`. -/
abbrev filteredAssociatedGradedHomotopyToDerivedFunctor :
    KFilt ⥤ DGr :=
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
    (DerivedCategory.Qh : HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ) ⥤ DGr)

section DerivedGradedObject

variable [HasDerivedCategory 𝒜]

private noncomputable abbrev gradedObjectEvalMapDerivedCategory (p : ℤ) :
    DGr ⥤ DerivedCategory 𝒜 :=
  (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜).mapDerivedCategory

/-- The bridge/view functor `D(Gr(\mathcal A)) ⥤ Gr(D(\mathcal A))` obtained by derived
evaluation in each degree. -/
abbrev gradedDerivedObjectFunctor :
    DGr ⥤ GradedObject ℤ (DerivedCategory 𝒜) where
  obj K := fun p ↦ (gradedObjectEvalMapDerivedCategory p).obj K
  map f := fun p ↦ (gradedObjectEvalMapDerivedCategory p).map f
  map_id X := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp

section DerivedPiece

/-- The `p`-th graded piece functor from `K(Fil^f(\mathcal A))` to `D(\mathcal A)`. -/
abbrev filteredGradedPieceHomotopyToDerivedFunctor (p : ℤ) :
    KFilt ⥤ DerivedCategory 𝒜 :=
  filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
    (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
      (DerivedCategory.Qh : HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory 𝒜)

/-- Bridge/view comparison on the homotopy side: evaluating after passage to
`D(Gr(\mathcal A))` agrees with first taking the `p`-th graded piece and then localizing. -/
noncomputable abbrev filteredGradedPieceHomotopyToDerivedFunctorCompIso (p : ℤ) :
    filteredAssociatedGradedHomotopyToDerivedFunctor ⋙
        gradedObjectEvalMapDerivedCategory p ≅
      filteredAssociatedGradedHomotopyFunctor 𝒜 ⋙
        (GradedObject.eval p).mapHomotopyCategory (up ℤ) ⋙
          (DerivedCategory.Qh : HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory 𝒜) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (filteredAssociatedGradedHomotopyFunctor 𝒜)
      ((GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜).mapDerivedCategoryFactorsh) ≪≫
    (Functor.associator _ _ _).symm

end DerivedPiece

end DerivedGradedObject

end AssociatedGraded

section Forget

variable [HasDerivedCategory 𝒜]

/-- The forgetful functor from `K(Fil^f(\mathcal A))` to `D(\mathcal A)`. -/
abbrev filteredForgetHomotopyToDerivedFunctor :
    KFilt ⥤ DerivedCategory 𝒜 :=
  ((finiteFilteredObjectForgetFunctor 𝒜 : FilF ⥤ 𝒜).mapHomotopyCategory (up ℤ)) ⋙
    DerivedCategory.Qh

end Forget

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: a filtered quasi-isomorphism is, by definition, a quasi-isomorphism after
-- applying the associated graded functor, and `DerivedCategory.Qh` inverts quasi-isomorphisms.
/-- The associated graded functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredAssociatedGradedHomotopyToDerivedFunctor : KFilt ⥤ DGr) := sorry

end AssociatedGraded

section GradedPiece

variable [HasDerivedCategory 𝒜]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: a filtered quasi-isomorphism becomes a quasi-isomorphism after taking associated
-- graded objects, evaluation at `p` preserves quasi-isomorphisms degreewise, and `Qh` localizes
-- at quasi-isomorphisms.
/-- The `p`-th graded piece functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredGradedPieceHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms (p : ℤ) :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredGradedPieceHomotopyToDerivedFunctor p : KFilt ⥤ DerivedCategory 𝒜) := sorry

/-- Lemma 13.13.6: the `p`-th graded-piece functor on `K(Fil^f(\mathcal A))` descends directly
to the canonical exact functor `DF(\mathcal A) ⥤ D(\mathcal A)` induced by `gr^p`. -/
abbrev filteredDerivedGradedPieceFunctor (p : ℤ) :
    DFilt ⥤ DerivedCategory 𝒜 :=
  Localization.lift
    (filteredGradedPieceHomotopyToDerivedFunctor p)
    (filteredGradedPieceHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms p)
    QFilt

/-- Textbook surface notation for the descended graded-piece functor `DF(\mathcal A) ⥤
D(\mathcal A)`. -/
scoped notation:max "gr^{" p "}" => filteredDerivedGradedPieceFunctor p

/-- The descended `p`-th graded piece functor commutes with shifts. -/
noncomputable instance filteredDerivedGradedPieceFunctor_commShift (p : ℤ) :
    (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ := sorry

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the source-facing `gr^p` on `DF(\mathcal A)` is itself a localization lift of the
-- homotopy-level `gr^p`, so Lemma 13.5.7 applies directly. The bridge
-- `DF(\mathcal A) ⥤ Gr(D(\mathcal A))` is only a companion comparison.
/-- The descended `p`-th graded piece functor is exact. -/
instance filteredDerivedGradedPieceFunctor_isTriangulated (p : ℤ) :
    (gr^{p} : DFilt ⥤ DerivedCategory 𝒜).IsTriangulated := sorry

end Exact

end GradedPiece

section Forget

variable [HasDerivedCategory 𝒜]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: if a morphism is a filtered quasi-isomorphism, then its cone is filtered acyclic.
-- Lemma 13.13.4 identifies this with the filtered acyclic subcategory, and the forgetful functor
-- sends filtered acyclic complexes to acyclic complexes, so `DerivedCategory.Qh` inverts it.
/-- The forgetful functor to the derived category inverts filtered quasi-isomorphisms. -/
theorem filteredForgetHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms :
    (FQis(𝒜) : MorphismProperty KFilt).IsInvertedBy
      (filteredForgetHomotopyToDerivedFunctor : KFilt ⥤ DerivedCategory 𝒜) := sorry

end Forget

section AssociatedGraded

variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Lemma 13.13.6: the associated graded functor on `K(Fil^f(\mathcal A))` descends to a
canonical exact functor `DF(\mathcal A) ⥤ D(Gr(\mathcal A))` commuting with the localization
functor. -/
abbrev filteredDerivedAssociatedGradedFunctor :
    DFilt ⥤ DGr :=
  Localization.lift
    filteredAssociatedGradedHomotopyToDerivedFunctor
    filteredAssociatedGradedHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
    QFilt

/-- Textbook surface notation for the descended associated-graded functor
`DF(\mathcal A) ⥤ D(Gr(\mathcal A))`. -/
scoped notation "gr" => filteredDerivedAssociatedGradedFunctor

/-- The descended associated graded functor commutes with shifts. -/
noncomputable instance filteredDerivedAssociatedGradedFunctor_commShift :
    (gr : DFilt ⥤ DGr).CommShift ℤ :=
  by
    sorry

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the functor on the homotopy category obtained from the associated graded functor
-- is exact, and Lemma 13.5.7 upgrades exactness to the localization lift.
/-- The descended associated graded functor is exact. -/
theorem filteredDerivedAssociatedGradedFunctor_isTriangulated :
    (gr : DFilt ⥤ DGr).IsTriangulated := sorry

/-- The canonical exactness instance for the descended associated graded functor. -/
instance :
    (gr : DFilt ⥤ DGr).IsTriangulated :=
  filteredDerivedAssociatedGradedFunctor_isTriangulated

end Exact

end AssociatedGraded

section GradedDerivedObject

variable [HasDerivedCategory 𝒜]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- Companion bridge/view for Lemma 13.13.6: package the descended associated graded functor as a
graded object in `D(\mathcal A)`. Its degree-`p` evaluation is compared to the source-facing
functor `gr^{p}` by `filteredDerivedGradedFunctorEvalIso`. -/
abbrev filteredDerivedGradedFunctor :
    DFilt ⥤ GradedObject ℤ (DerivedCategory 𝒜) :=
  gr ⋙ gradedDerivedObjectFunctor

section GradedPiece

/-- Evaluating the graded-object bridge in degree `p` recovers the source-facing descended
graded-piece functor `gr^p`. -/
noncomputable abbrev filteredDerivedGradedFunctorEvalIso (p : ℤ) :
    filteredDerivedGradedFunctor ⋙
        (GradedObject.eval p : GradedObject ℤ (DerivedCategory 𝒜) ⥤ DerivedCategory 𝒜) ≅
      gr^{p} :=
  by
    simpa [filteredDerivedGradedFunctor, gradedDerivedObjectFunctor] using
      (Localization.liftNatIso
        QFilt
        (FQis(𝒜) : MorphismProperty KFilt)
        (filteredAssociatedGradedHomotopyToDerivedFunctor ⋙
          gradedObjectEvalMapDerivedCategory p)
        (filteredGradedPieceHomotopyToDerivedFunctor p)
        (gr ⋙ gradedObjectEvalMapDerivedCategory p)
        (gr^{p})
        (filteredGradedPieceHomotopyToDerivedFunctorCompIso p))

end GradedPiece

end GradedDerivedObject

section Forget

variable [HasDerivedCategory 𝒜]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/-- The forgetful functor on `DF(\mathcal A)`. -/
abbrev filteredDerivedForgetFunctor :
    DFilt ⥤ DerivedCategory 𝒜 :=
  Localization.lift
    filteredForgetHomotopyToDerivedFunctor
    filteredForgetHomotopyToDerivedFunctor_inverts_filteredQuasiIsomorphisms
    QFilt

/-- The descended forgetful functor commutes with shifts. -/
noncomputable instance filteredDerivedForgetFunctor_commShift :
    (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).CommShift ℤ :=
  by
    sorry

section Exact

variable [IsTriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

-- Proof sketch: the forgetful functor on filtered complexes is exact on the homotopy category,
-- and once it is known to invert filtered quasi-isomorphisms, Lemma 13.5.7 gives exactness of
-- the descended localization lift.
/-- The descended forgetful functor is exact. -/
instance filteredDerivedForgetFunctor_isTriangulated :
    (filteredDerivedForgetFunctor : DFilt ⥤ DerivedCategory 𝒜).IsTriangulated := sorry

end Exact

end Forget

end CategoryTheory

/-! ### Definition_13_13_7 (from Chap13) -/
noncomputable section

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)] [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
variable [HasDerivedCategory (GradedObject ℤ 𝒜)]
variable [Pretriangulated (HomotopyCategory (finiteFilteredObjectCat 𝒜) (up ℤ))]

/- Domain-style sampling for Definition `13.13.7`.
- primary domain: bounded full subcategories of the filtered derived category cut out by the
  cohomological boundedness of the single associated graded object in `D(Gr(\mathcal A))`;
- sampled owner declarations:
  `filteredDerivedCategory`,
  `gr`,
  `t.plus`,
  `t.bounded`;
- best owner abstraction: the source-facing owners are the bounded full subcategories of the
  chapter owner `filteredDerivedCategory 𝒜`, cut out by pulling back the canonical boundedness
  owners on `D(Gr(\mathcal A))` along the associated-graded functor
  `gr : DF(𝒜) ⥤ D(Gr(𝒜))` from Lemma `13.13.6`;
- primitive data: the canonical boundedness owners `t.plus`, `t.minus`, and `t.bounded` on
  `D(GradedObject ℤ 𝒜)`, together with the canonical bridge
  `gr`;
- derived API: the pulled-back boundedness predicates on `DF(𝒜)`, kept as the reusable
  bridge/view owners for downstream restriction functors, and the bounded full subcategories
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the bounded-below, bounded-above, and bounded filtered derived categories
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)`;
- `core/canonical`: the chapter owner `filteredDerivedCategory 𝒜`, the boundedness owners
  `t.plus`, `t.minus`, and `t.bounded` on `D(GradedObject ℤ 𝒜)`;
- `bridge/view`: the associated-graded bridge `gr : DF(𝒜) ⥤ D(Gr(𝒜))`;
  the further comparison `filteredDerivedGradedFunctor : DF(𝒜) ⥤ Gr(D(𝒜))` is only a derived
  graded-piece view, not the owner used to define boundedness here.

This item therefore keeps the actual chapter owner `DF(𝒜)` at the public surface and uses the
associated-graded functor to `D(Gr(\mathcal A))` as bridge data, rather than replacing the source
definition by the weaker degreewise condition in `Gr(D(\mathcal A))`. -/

local notation "DGr" => DerivedCategory (GradedObject ℤ 𝒜)

variable (𝒜) in
/- Companion recall: the filtered derived category `DF(𝒜)` is the canonical owner from
Definition `13.13.5`. -/
#check (DF(𝒜))

variable (𝒜) in
/-- The bounded-below object property on `DF(𝒜)` cut out by the canonical bounded-below
owner `t.plus` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedPlusProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.plus : ObjectProperty DGr).inverseImage
    (filteredDerivedAssociatedGradedFunctor : DF(𝒜) ⥤ DGr)

variable (𝒜) in
/-- The bounded-above object property on `DF(𝒜)` cut out by the canonical bounded-above
owner `t.minus` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedMinusProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.minus : ObjectProperty DGr).inverseImage
    (filteredDerivedAssociatedGradedFunctor : DF(𝒜) ⥤ DGr)

variable (𝒜) in
/-- The bounded object property on `DF(𝒜)` cut out by the canonical boundedness owner
`t.bounded` on `D(Gr(\mathcal A))` via the associated-graded functor. -/
abbrev filteredDerivedBoundedProperty :
    ObjectProperty (DF(𝒜)) :=
  (t.bounded : ObjectProperty DGr).inverseImage
    (filteredDerivedAssociatedGradedFunctor : DF(𝒜) ⥤ DGr)

variable (𝒜) in
/-- The bounded-below filtered derived category `DF⁺(𝒜)` cut out by associated graded objects in
`D⁺(Gr(\mathcal A))`. This is a single bounded-below condition on `gr(X)` in
`D(Gr(\mathcal A))`, not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedBelowFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedPlusProperty 𝒜).FullSubcategory

variable (𝒜) in
/-- The bounded-above filtered derived category `DF⁻(𝒜)` cut out by associated graded objects in
`D⁻(Gr(\mathcal A))`. This is a single bounded-above condition on `gr(X)` in
`D(Gr(\mathcal A))`, not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedAboveFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedMinusProperty 𝒜).FullSubcategory

variable (𝒜) in
/-- The bounded filtered derived category `DFᵇ(𝒜)` cut out by associated graded objects in
`Dᵇ(Gr(\mathcal A))`. This is a single bounded condition on `gr(X)` in `D(Gr(\mathcal A))`,
not degreewise boundedness of the pieces `gr^p(X)`. -/
abbrev boundedFilteredDerivedCategory :
    Type (max u v) :=
  (filteredDerivedBoundedProperty 𝒜).FullSubcategory

scoped notation "DF⁺(" A:arg ")" => boundedBelowFilteredDerivedCategory A
scoped notation "DF⁻(" A:arg ")" => boundedAboveFilteredDerivedCategory A
scoped notation "DFᵇ(" A:arg ")" => boundedFilteredDerivedCategory A

/- Definition `13.13.7`: the chapter owners `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)` are the bounded
full subcategories of `DF(𝒜)` cut out by the canonical associated-graded functor
`gr : DF(𝒜) ⥤ D(Gr(\mathcal A))` from Lemma `13.13.6`. -/
#check (filteredDerivedPlusProperty 𝒜)
#check (filteredDerivedMinusProperty 𝒜)
#check (filteredDerivedBoundedProperty 𝒜)
#check (DF⁺(𝒜))
#check (DF⁻(𝒜))
#check (DFᵇ(𝒜))

end CategoryTheory

/-! ### Lemma_13_13_8 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open scoped CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace FilteredComplex

open FilteredObject

/-
Domain-style sampling for Lemma `13.13.8`.
- primary domain: filtered cochain complexes with finite filtrations, their associated graded
  complexes, and canonical truncation maps on the underlying cochain complex;
- sampled owner declarations in this domain:
  `FilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.associatedGraded`,
  `FilteredComplex.associatedGradedMap`,
  `FilteredComplex.underlyingMap`,
  `QuasiIso`,
  `CochainComplex.πTruncGE`,
  `CochainComplex.ιTruncLE`,
  `CochainComplex.truncGEMap`;
- best owner abstraction: the Chapter `12` owner `FilteredComplex 𝒜`, with the finite-filtration
  hypothesis `K.HasFiniteFiltrations`; the associated-graded comparison lives intrinsically on
  filtered-complex morphisms via `associatedGradedMap`, while the canonical truncations live on
  the underlying cochain complex `K.underlying`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`;
- derived API: the associated graded complex `K.associatedGraded`, the associated-graded map
  `associatedGradedMap f`, the owner-level underlying map `underlyingMap f`, and the canonical
  truncation objects/maps on `K.underlying`, `K.underlying.truncGE a`, `K.underlying.truncLE b`,
  `K.underlying.πTruncGE a`, `K.underlying.ιTruncLE b`, and
  `truncGEMap (K.underlying.ιTruncLE b) a`;
- source/core/bridge triage:
  `source-facing`: vanishing of the cohomology of `gr(K^•)` and the bounded filtered truncation
    replacements;
  `core/canonical`: `FilteredComplex`, `HasFiniteFiltrations`, `associatedGraded`,
    `associatedGradedMap`, `QuasiIso`, and the ordinary cochain-complex truncation owners on
    `K.underlying`;
  `bridge/view`: the comparison from a filtered replacement to the canonical underlying
    truncation.

This file therefore keeps the public statements on the intrinsic owner `FilteredComplex 𝒜`,
retains the finite-filtration hypothesis explicitly, and expresses filtered quasi-isomorphism data
by the canonical condition `QuasiIso (associatedGradedMap f)`. The ordinary truncation owners on
`K.underlying` remain proof-level bridge data rather than part of the public API surface. -/

/-- Lemma 13.13.8 (1): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `< a`, then there exists a filtered
quasi-isomorphism from `K` to a filtered complex whose underlying complex is bounded below by
`a`. -/
theorem exists_filteredQuasiIso_to_boundedBelow_of_associatedGradedCohomologyVanishesBelow
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hgr : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    ∃ (L : FilteredComplex 𝒜) (_ : L.HasFiniteFiltrations) (f : K ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ L.underlying.IsStrictlyGE a := by
  sorry

/-- Lemma 13.13.8 (2): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `> b`, then there exists a filtered
quasi-isomorphism to `K` from a filtered complex whose underlying complex is bounded above by
`b`. -/
theorem exists_filteredQuasiIso_from_boundedAbove_of_associatedGradedCohomologyVanishesAbove
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hgr : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ (M : FilteredComplex 𝒜) (_ : M.HasFiniteFiltrations) (g : M ⟶ K),
      QuasiIso (associatedGradedMap g) ∧ M.underlying.IsStrictlyLE b := by
  sorry

/-- Lemma 13.13.8 (3): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology for `|n| ≫ 0`, then there exists a commutative square of filtered
quasi-isomorphisms
`K ⟶ L`, `M ⟶ K`, `M ⟶ N`, `N ⟶ L`
with `L` bounded below, `M` bounded above, and `N` bounded. -/
theorem exists_filteredQuasiIso_square_with_boundedRepresentatives_of_associatedGradedCohomologyEventuallyVanishes
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations)
    (hgr : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ a b : ℤ,
      ∃ (L : FilteredComplex 𝒜) (_ : L.HasFiniteFiltrations) (f : K ⟶ L)
        (M : FilteredComplex 𝒜) (_ : M.HasFiniteFiltrations) (g : M ⟶ K)
        (N : FilteredComplex 𝒜) (_ : N.HasFiniteFiltrations)
        (u : M ⟶ N) (v : N ⟶ L),
        QuasiIso (associatedGradedMap f) ∧
          QuasiIso (associatedGradedMap g) ∧
          QuasiIso (associatedGradedMap u) ∧
          QuasiIso (associatedGradedMap v) ∧
          CommSq u g v f ∧
          L.underlying.IsStrictlyGE a ∧
          M.underlying.IsStrictlyLE b ∧
          N.underlying.IsStrictlyGE a ∧
          N.underlying.IsStrictlyLE b := by
  sorry

end FilteredComplex

end CategoryTheory

/-! ### Lemma_13_13_9 (from Chap13) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

/- Domain-style sampling for Lemma `13.13.9`.
- primary domain: bounded filtered homotopy categories, filtered acyclic complexes, filtered
  quasi-isomorphisms, and their localization in the filtered derived category;
- sampled owner declarations:
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)`,
  `FQis(𝒜)`,
  `FAc(𝒜)`,
  `MorphismProperty.Q`,
  `boundedBelowHomotopyProperty`,
  `boundedAboveHomotopyProperty`,
  `boundedHomotopyProperty`;
- best owner abstraction: the source-facing derived owners are already the chapter notations
  `DF⁺(𝒜)`, `DF⁻(𝒜)`, and `DFᵇ(𝒜)` from Definition `13.13.7`; this lemma should therefore live
  at the bridge/view layer, expressing the bounded filtered localizations of
  `K⁺(Fil^f(𝒜))`, `K⁻(Fil^f(𝒜))`, and `Kᵇ(Fil^f(𝒜))` into those existing owners rather than
  introducing a second bounded filtered derived-category owner;
- primitive data: the chapter owners `FQis(𝒜)`, `FAc(𝒜)`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW).Q`,
  together with the bounded homotopy object properties on `K(Fil^f(𝒜))`;
- derived API: the bounded filtered quasi-isomorphism owners `FQis⁺/⁻/ᵇ`, the notation-only
  bounded filtered acyclic views `FAc⁺/⁻/ᵇ`, and the canonical bounded bridge functors
  `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)`, `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)`, `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)`.

Source/core/bridge triage:
- `source-facing`: the bounded filtered localization statements of Lemma `13.13.9`;
- `core/canonical`: `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)`, `FQis(𝒜)`, `FAc(𝒜)`,
  `((FAc(𝒜) : ObjectProperty KFilt).trW.Q : KFilt ⥤ DF(𝒜))`, and the bounded homotopy owners on
  `K(Fil^f(𝒜))`;
- `bridge/view`: the bounded filtered quasi-isomorphism owners, the notation-only restricted
  acyclic views, and the induced functors from bounded filtered homotopy categories into the
  existing bounded filtered derived categories. -/

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]
variable [HasBinaryBiproducts (finiteFilteredObjectCat 𝒜)]
variable [Pretriangulated (HomotopyCategory (GradedObject ℤ 𝒜) (up ℤ))]

local notation "FilF" => finiteFilteredObjectCat 𝒜
local notation "KFilt" => HomotopyCategory FilF (up ℤ)

local instance finiteFiltered_hasFiniteBiproducts_13_13_9 : HasFiniteBiproducts FilF :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

local instance pretriangulated_filtered_homotopy_13_13_9 : Pretriangulated KFilt := by
  exact finiteFilteredHomotopyPretriangulated

local instance isTriangulated_filtered_homotopy_13_13_9 : IsTriangulated KFilt := by
  exact finiteFilteredHomotopyIsTriangulated

private abbrev QFilt : KFilt ⥤ DF(𝒜) :=
  (((FAc(𝒜) : ObjectProperty KFilt).trW).Q : KFilt ⥤ DF(𝒜))

local instance qFilt_commShift :
    ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)).CommShift ℤ := by
  infer_instance

local instance qFilt_isTriangulated :
    ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)).IsTriangulated := by
  infer_instance

local instance :
    ((((HomotopyCategory.plus FilF).ι : K⁺(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).CommShift ℤ := by
  infer_instance

local instance :
    ((((HomotopyCategory.plus FilF).ι : K⁺(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).IsTriangulated := by
  infer_instance

local instance :
    ((((HomotopyCategory.minus FilF).ι : K⁻(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).CommShift ℤ := by
  infer_instance

local instance :
    ((((HomotopyCategory.minus FilF).ι : K⁻(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).IsTriangulated := by
  infer_instance

local instance :
    ((((HomotopyCategory.bounded FilF).ι : Kᵇ(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).CommShift ℤ := by
  infer_instance

local instance :
    ((((HomotopyCategory.bounded FilF).ι : Kᵇ(FilF) ⥤ KFilt) ⋙
      ((((FAc(𝒜) : ObjectProperty KFilt).trW).Q) : KFilt ⥤ DF(𝒜)))).IsTriangulated := by
  infer_instance

/- The filtered quasi-isomorphisms in `K^+(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedBelowFilteredQuasiIso :
    MorphismProperty (K⁺(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.plus FilF).ι

/- The filtered quasi-isomorphisms in `K^-(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedAboveFilteredQuasiIso :
    MorphismProperty (K⁻(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.minus FilF).ι

/- The filtered quasi-isomorphisms in `K^b(\mathrm{Fil}^f(\mathcal A))` are the morphisms whose
images in `K(\mathrm{Fil}^f(\mathcal A))` are filtered quasi-isomorphisms. -/
variable (𝒜) in
abbrev boundedFilteredQuasiIso :
    MorphismProperty (Kᵇ(FilF)) :=
  (FQis(𝒜) : MorphismProperty KFilt).inverseImage
    (HomotopyCategory.bounded FilF).ι

scoped notation "FQis⁺(" A:arg ")" => boundedBelowFilteredQuasiIso A
scoped notation "FQis⁻(" A:arg ")" => boundedAboveFilteredQuasiIso A
scoped notation "FQisᵇ(" A:arg ")" => boundedFilteredQuasiIso A
scoped notation "FAc⁺(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.plus (finiteFilteredObjectCat A)))
scoped notation "FAc⁻(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.minus (finiteFilteredObjectCat A)))
scoped notation "FAcᵇ(" A:arg ")" =>
  ObjectProperty.inverseImage
    (FAc(A))
    (ObjectProperty.ι (HomotopyCategory.bounded (finiteFilteredObjectCat A)))

-- Proof sketch: the associated graded functor on filtered homotopy categories preserves
-- bounded-below complexes, and Lemma `13.11.6 (1)` shows that the derived image of a bounded-
-- below graded complex lies in `D⁺(Gr(\mathcal A))`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded-below filtered
homotopy objects to `DF⁺(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedBelowFilteredDerivedCategory
    (X : K⁺(FilF)) :
    filteredDerivedPlusProperty 𝒜
      (QFilt.obj X.obj) := by
  sorry

-- Proof sketch: the same argument with bounded-above associated graded complexes lands in
-- `D⁻(Gr(\mathcal A))`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded-above filtered
homotopy objects to `DF⁻(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedAboveFilteredDerivedCategory
    (X : K⁻(FilF)) :
    filteredDerivedMinusProperty 𝒜
      (QFilt.obj X.obj) := by
  sorry

-- Proof sketch: a bounded filtered homotopy object has bounded associated graded complex, so its
-- image in `DF(\mathcal A)` lies in `DFᵇ(\mathcal A)`.
variable (𝒜) in
/-- The canonical functor `K(Fil^f(\mathcal A)) ⟶ DF(\mathcal A)` sends bounded filtered homotopy
objects to `DFᵇ(\mathcal A)`. -/
theorem filteredDerivedQuotientFunctor_obj_mem_boundedFilteredDerivedCategory
    (X : Kᵇ(FilF)) :
    filteredDerivedBoundedProperty 𝒜
      (QFilt.obj X.obj) := by
  sorry

variable (𝒜) in
/-- The canonical functor `K^+(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^+(\mathcal A)`. -/
abbrev mapBoundedBelowFilteredHomotopyToDerivedBelow :
    K⁺(FilF) ⥤ DF⁺(𝒜) :=
  (filteredDerivedPlusProperty 𝒜).lift
    ((HomotopyCategory.plus FilF).ι ⋙ QFilt)
    (fun X ↦ by
      simpa using filteredDerivedQuotientFunctor_obj_mem_boundedBelowFilteredDerivedCategory 𝒜 X)

variable (𝒜) in
/-- The canonical functor `K^-(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^-(\mathcal A)`. -/
abbrev mapBoundedAboveFilteredHomotopyToDerivedAbove :
    K⁻(FilF) ⥤ DF⁻(𝒜) :=
  (filteredDerivedMinusProperty 𝒜).lift
    ((HomotopyCategory.minus FilF).ι ⋙ QFilt)
    (fun X ↦ by
      simpa using filteredDerivedQuotientFunctor_obj_mem_boundedAboveFilteredDerivedCategory 𝒜 X)

variable (𝒜) in
/-- The canonical functor `K^b(\mathrm{Fil}^f(\mathcal A)) ⟶ DF^b(\mathcal A)`. -/
abbrev mapBoundedFilteredHomotopyToDerivedBounded :
    Kᵇ(FilF) ⥤ DFᵇ(𝒜) :=
  (filteredDerivedBoundedProperty 𝒜).lift
    ((HomotopyCategory.bounded FilF).ι ⋙ QFilt)
    (fun X ↦ by
      simpa using filteredDerivedQuotientFunctor_obj_mem_boundedFilteredDerivedCategory 𝒜 X)

/- Companion recall: the acyclic bounded-below objects define a triangulated full subcategory
`FAc^{+}(\mathcal A) ⊆ K^{+}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
triangulated instance applied to `FAc(𝒜)`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (FAc⁺(𝒜)))

/- Companion recall: the acyclic bounded-below subcategory `FAc^{+}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{+}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
retract stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (FAc⁺(𝒜)) from by
  dsimp [filteredAcyclic]
  infer_instance)

/- Companion recall: the acyclic bounded-above objects define a triangulated full subcategory
`FAc^{-}(\mathcal A) ⊆ K^{-}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
triangulated instance applied to `FAc(𝒜)`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (FAc⁻(𝒜)))

/- Companion recall: the acyclic bounded-above subcategory `FAc^{-}(\mathcal A)` is saturated,
i.e. stable under retracts in `K^{-}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
retract stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (FAc⁻(𝒜)) from by
  dsimp [filteredAcyclic]
  infer_instance)

/- Companion recall: the acyclic bounded objects define a triangulated full subcategory
`FAc^{b}(\mathcal A) ⊆ K^{b}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
triangulated instance applied to `FAc(𝒜)`. -/
#check (inferInstance : ObjectProperty.IsTriangulated (FAcᵇ(𝒜)))

/- Companion recall: the acyclic bounded subcategory `FAc^{b}(\mathcal A)` is saturated, i.e.
stable under retracts in `K^{b}(Fil^{f}(\mathcal A))`. This is the generic inverse-image
retract stability instance. -/
#check (show ObjectProperty.IsStableUnderRetracts (FAcᵇ(𝒜)) from by
  dsimp [filteredAcyclic]
  infer_instance)

-- Proof sketch: restrict Lemma `13.13.4` from `K(Fil^f(\mathcal A))` to the bounded-below full
-- subcategory, exactly as in Lemma `13.11.6 (1)`.
/-- Lemma 13.13.9 (1): the saturated multiplicative system corresponding to
`FAc^{+}(\mathcal A)` is precisely `FQis^{+}(\mathcal A)`. -/
theorem boundedBelowFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAc⁺(𝒜)).trW =
      FQis⁺(𝒜) := by
  sorry

-- Proof sketch: an object of `K^{+}(Fil^{f}(\mathcal A))` maps to zero in `DF^{+}(\mathcal A)`
-- exactly when its image in `DF(\mathcal A)` is filtered acyclic.
/-- Lemma 13.13.9 (2): the kernel of
`K^{+}(Fil^{f}(\mathcal A)) ⟶ DF^{+}(\mathcal A)` is `FAc^{+}(\mathcal A)`. -/
theorem kernel_mapBoundedBelowFilteredHomotopyToDerivedBelow_eq_acyclic :
    Functor.kernel (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜) =
      FAc⁺(𝒜) := by
  sorry

-- Proof sketch: use Lemma `13.13.8 (1)` to obtain bounded-below filtered representatives and
-- then repeat the localization argument of Lemma `13.11.6 (3)`.
/-- Lemma 13.13.9 (3): the canonical functor
`K^{+}(Fil^{f}(\mathcal A)) ⟶ DF^{+}(\mathcal A)` realizes `DF^{+}(\mathcal A)` as the
localization of `K^{+}(Fil^{f}(\mathcal A))` at `FQis^{+}(\mathcal A)`. -/
theorem mapBoundedBelowFilteredHomotopyToDerivedBelow_isLocalization :
    Functor.IsLocalization
      (mapBoundedBelowFilteredHomotopyToDerivedBelow 𝒜)
      (FQis⁺(𝒜)) := by
  sorry

-- Proof sketch: restrict Lemma `13.13.4` to the bounded-above full subcategory, as in
-- Lemma `13.11.6 (4)`.
/-- Lemma 13.13.9 (4): the saturated multiplicative system corresponding to
`FAc^{-}(\mathcal A)` is precisely `FQis^{-}(\mathcal A)`. -/
theorem boundedAboveFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAc⁻(𝒜)).trW =
      FQis⁻(𝒜) := by
  sorry

-- Proof sketch: bounded-above filtered objects die in `DF^{-}(\mathcal A)` exactly when their
-- ambient filtered derived objects are filtered acyclic.
/-- Lemma 13.13.9 (5): the kernel of
`K^{-}(Fil^{f}(\mathcal A)) ⟶ DF^{-}(\mathcal A)` is `FAc^{-}(\mathcal A)`. -/
theorem kernel_mapBoundedAboveFilteredHomotopyToDerivedAbove_eq_acyclic :
    Functor.kernel (mapBoundedAboveFilteredHomotopyToDerivedAbove 𝒜) =
      FAc⁻(𝒜) := by
  sorry

-- Proof sketch: use Lemma `13.13.8 (2)` to obtain bounded-above filtered representatives and
-- then repeat the localization argument of Lemma `13.11.6 (6)`.
/-- Lemma 13.13.9 (6): the canonical functor
`K^{-}(Fil^{f}(\mathcal A)) ⟶ DF^{-}(\mathcal A)` realizes `DF^{-}(\mathcal A)` as the
localization of `K^{-}(Fil^{f}(\mathcal A))` at `FQis^{-}(\mathcal A)`. -/
theorem mapBoundedAboveFilteredHomotopyToDerivedAbove_isLocalization :
    Functor.IsLocalization
      (mapBoundedAboveFilteredHomotopyToDerivedAbove 𝒜)
      (FQis⁻(𝒜)) := by
  sorry

-- Proof sketch: restrict Lemma `13.13.4` to the bounded full subcategory, as in
-- Lemma `13.11.6 (7)`.
/-- Lemma 13.13.9 (7): the saturated multiplicative system corresponding to
`FAc^{b}(\mathcal A)` is precisely `FQis^{b}(\mathcal A)`. -/
theorem boundedFilteredAcyclicProperty_trW_eq_quasiIso :
    (FAcᵇ(𝒜)).trW =
      FQisᵇ(𝒜) := by
  sorry

-- Proof sketch: a bounded filtered homotopy object becomes zero in `DF^{b}(\mathcal A)` exactly
-- when it is filtered acyclic.
/-- Lemma 13.13.9 (8): the kernel of
`K^{b}(Fil^{f}(\mathcal A)) ⟶ DF^{b}(\mathcal A)` is `FAc^{b}(\mathcal A)`. -/
theorem kernel_mapBoundedFilteredHomotopyToDerivedBounded_eq_acyclic :
    Functor.kernel (mapBoundedFilteredHomotopyToDerivedBounded 𝒜) =
      FAcᵇ(𝒜) := by
  sorry

-- Proof sketch: use Lemma `13.13.8 (3)` to choose bounded filtered representatives and then
-- repeat the bounded localization argument of Lemma `13.11.6 (9)`.
/-- Lemma 13.13.9 (9): the canonical functor
`K^{b}(Fil^{f}(\mathcal A)) ⟶ DF^{b}(\mathcal A)` realizes `DF^{b}(\mathcal A)` as the
localization of `K^{b}(Fil^{f}(\mathcal A))` at `FQis^{b}(\mathcal A)`. -/
theorem mapBoundedFilteredHomotopyToDerivedBounded_isLocalization :
    Functor.IsLocalization
      (mapBoundedFilteredHomotopyToDerivedBounded 𝒜)
      (FQisᵇ(𝒜)) := by
  sorry

end CategoryTheory
